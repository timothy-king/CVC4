/*********************                                                        */
/*! \file dio_solver.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Tim King
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Diophantine equation solver
 **
 ** A Diophantine equation solver for the theory of arithmetic.
 **/

#include "theory/arith/dio_solver.h"
#include "theory/arith/options.h"

#include <iostream>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

inline Node makeIntegerVariable(){
  NodeManager* curr = NodeManager::currentNM();
  return curr->mkSkolem("intvar", curr->integerType(), "is an integer variable created by the dio solver");
}

DioSolver::DioSolver(context::Context* ctxt) :
  d_lastUsedProofVariable(ctxt,0),
  d_inputConstraints(ctxt),
  d_nextInputConstraintToEnqueue(ctxt, 0),
  d_trail(ctxt),
  d_subs(ctxt),
  d_elimPos(ctxt),
  d_currentF(),
  d_savedQueue(ctxt),
  d_savedQueueIndex(ctxt, 0),
  d_conflictHasBeenRaised(ctxt, false),
  d_maxInputCoefficientLength(ctxt, 0),
  d_usedDecomposeIndex(ctxt, false),
  d_lastPureSubstitution(ctxt, 0),
  d_pureSubstitionIter(ctxt, 0),
  d_decompositionLemmaQueue(ctxt),
  d_smallPrimes(NULL),
  d_singleVarCutsInARow(0)
{}

DioSolver::~DioSolver(){
  if( d_smallPrimes != NULL) {
    delete d_smallPrimes;
  }
}

DioSolver::Statistics::Statistics() :
  d_conflictCalls("theory::arith::dio::conflictCalls",0),
  d_cutCalls("theory::arith::dio::cutCalls",0),
  d_cuts("theory::arith::dio::cuts",0),
  d_conflicts("theory::arith::dio::conflicts",0),
  d_conflictTimer("theory::arith::dio::conflictTimer"),
  d_cutTimer("theory::arith::dio::cutTimer"),

  d_enqueueInputConstraintsTimer("zz::enqueueInputConstraintsTimer"),
  d_pushInputConstraintsTimer("zz::pushInputConstraintsTimer"),
  d_scaleEqAtIndexTimer("zz::scaleEqAtIndexTimer"),
  d_moveMinimumByAbsToQueueFrontTimer("zz::moveMinimumByAbsToQueueFrontTimer"),
  d_impliedGcdOfOneTimer("zz::impliedGcdOfOneTimer"),
  d_columnGcdIsOneTimer("zz::columnGcdIsOneTimer"),
  d_solveIndexTimer("zz::solveIndexTimer"),
  d_reduceByGCDTimer("zz::reduceByGCDTimer"),
  d_subAndReduceCurrentFByIndexTimer("zz::subAndReduceCurrentFByIndexTimer")
{
  StatisticsRegistry::registerStat(&d_conflictCalls);
  StatisticsRegistry::registerStat(&d_cutCalls);

  StatisticsRegistry::registerStat(&d_cuts);
  StatisticsRegistry::registerStat(&d_conflicts);

  StatisticsRegistry::registerStat(&d_conflictTimer);
  StatisticsRegistry::registerStat(&d_cutTimer);

  
  StatisticsRegistry::registerStat(&d_enqueueInputConstraintsTimer);
  StatisticsRegistry::registerStat(&d_pushInputConstraintsTimer);
  StatisticsRegistry::registerStat(&d_scaleEqAtIndexTimer);
  StatisticsRegistry::registerStat(&d_moveMinimumByAbsToQueueFrontTimer);
  StatisticsRegistry::registerStat(&d_impliedGcdOfOneTimer);
  StatisticsRegistry::registerStat(&d_columnGcdIsOneTimer);
  StatisticsRegistry::registerStat(&d_solveIndexTimer);
  StatisticsRegistry::registerStat(&d_reduceByGCDTimer);
  StatisticsRegistry::registerStat(&d_subAndReduceCurrentFByIndexTimer);
}

DioSolver::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_conflictCalls);
  StatisticsRegistry::unregisterStat(&d_cutCalls);

  StatisticsRegistry::unregisterStat(&d_cuts);
  StatisticsRegistry::unregisterStat(&d_conflicts);

  StatisticsRegistry::unregisterStat(&d_conflictTimer);
  StatisticsRegistry::unregisterStat(&d_cutTimer);

  StatisticsRegistry::unregisterStat(&d_enqueueInputConstraintsTimer);
  StatisticsRegistry::unregisterStat(&d_pushInputConstraintsTimer);
  StatisticsRegistry::unregisterStat(&d_scaleEqAtIndexTimer);
  StatisticsRegistry::unregisterStat(&d_moveMinimumByAbsToQueueFrontTimer);
  StatisticsRegistry::unregisterStat(&d_impliedGcdOfOneTimer);
  StatisticsRegistry::unregisterStat(&d_columnGcdIsOneTimer);
  StatisticsRegistry::unregisterStat(&d_solveIndexTimer);
  StatisticsRegistry::unregisterStat(&d_reduceByGCDTimer);
  StatisticsRegistry::unregisterStat(&d_subAndReduceCurrentFByIndexTimer);
}

bool DioSolver::queueConditions(TrailIndex t){
  /* debugPrintTrail(t); */
  Debug("queueConditions") << !inConflict() << std::endl;
  Debug("queueConditions") << gcdIsOne(t) << std::endl;
  //This is no longer true of the queue
  Debug("queueConditions") << !debugAnySubstitionApplies(t) << std::endl;
  Debug("queueConditions") << !triviallySat(t) << std::endl;
  Debug("queueConditions") << !triviallyUnsat(t) << std::endl;

  return
    !inConflict() &&
    gcdIsOne(t) &&
    !debugAnySubstitionApplies(t) &&
    !triviallySat(t) &&
    !triviallyUnsat(t);
}

size_t DioSolver::allocateProofVariable() {
  Assert(d_lastUsedProofVariable <= d_proofVariablePool.size());
  if(d_lastUsedProofVariable == d_proofVariablePool.size()){
    Assert(d_lastUsedProofVariable == d_proofVariablePool.size());
    Node intVar = makeIntegerVariable();
    d_proofVariablePool.push_back(Variable(intVar));
  }
  size_t res = d_lastUsedProofVariable;
  d_lastUsedProofVariable = d_lastUsedProofVariable + 1;
  return res;
}


Node DioSolver::nextPureSubstitution(){
  Assert(hasMorePureSubstitutions());
  SubIndex curr = d_pureSubstitionIter;
  d_pureSubstitionIter = d_pureSubstitionIter + 1;

  Assert(d_subs[curr].d_fresh.isNull());
  Variable v = d_subs[curr].d_eliminated;

  SumPair sp = d_trail[d_subs[curr].d_constraint].d_eq;
  Polynomial p = sp.getPolynomial();
  Constant c = -sp.getConstant();
  Polynomial cancelV = p + Polynomial::mkPolynomial(v);
  Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, v.getNode(), cancelV.getNode());
  return eq;
}


bool DioSolver::debugEqualityInInputEquations(Node eq){
  typedef context::CDList<InputConstraint>::const_iterator const_iterator;
  const_iterator i=d_inputConstraints.begin(), end = d_inputConstraints.end();
  for(; i != end; ++i){
    Node reason_i = (*i).d_reason;
    if(eq == reason_i){
      return true;
    }
  }
  return false;
}


void DioSolver::pushInputConstraint(const Comparison& eq, Node reason){
  TimerStat::CodeTimer codeTimer(d_statistics.d_pushInputConstraintsTimer);

  Assert(!debugEqualityInInputEquations(reason));
  Assert(eq.debugIsIntegral());
  Assert(eq.getNode().getKind() == kind::EQUAL);

  SumPair sp = eq.toSumPair();
  uint32_t length = sp.maxLength();
  if(length > d_maxInputCoefficientLength){
    d_maxInputCoefficientLength = length;
  }

  size_t varIndex = allocateProofVariable();
  Variable proofVariable(d_proofVariablePool[varIndex]);
  //Variable proofVariable(makeIntegerVariable());

  TrailIndex posInTrail = d_trail.size();
  d_trail.push_back(Constraint(sp,Polynomial(Monomial(VarList(proofVariable)))));

  size_t posInConstraintList = d_inputConstraints.size();
  d_inputConstraints.push_back(InputConstraint(reason, posInTrail));

  d_varToInputConstraintMap[proofVariable.getNode()] = posInConstraintList;
}


DioSolver::TrailIndex DioSolver::scaleEqAtIndex(DioSolver::TrailIndex i, const Integer& g){
  TimerStat::CodeTimer codeTimer(d_statistics.d_scaleEqAtIndexTimer);
  Assert(g != 0);
  Constant invg = Constant::mkConstant(Rational(Integer(1),g));
  const SumPair& sp = d_trail[i].d_eq;
  const Polynomial& proof = d_trail[i].d_proof;

  SumPair newSP = sp * invg;
  Polynomial newProof = proof * invg;

  Assert(newSP.isIntegral());
  Assert(newSP.gcd() == 1);

  TrailIndex j = d_trail.size();

  d_trail.push_back(Constraint(newSP, newProof));

  Debug("arith::dio") << "scaleEqAtIndex(" << i <<","<<g<<")"<<endl;
  Debug("arith::dio") << "derived "<< newSP.getNode()
                      <<" with proof " << newProof.getNode() << endl;
  return j;
}

Node DioSolver::proveIndex(TrailIndex i){
  Assert(inRange(i));
  const Polynomial& proof = d_trail[i].d_proof;
  Assert(!proof.isConstant());

  NodeBuilder<> nb(kind::AND);
  for(Polynomial::iterator iter = proof.begin(), end = proof.end(); iter!= end; ++iter){
    Monomial m = (*iter);
    Assert(!m.isConstant());
    VarList vl = m.getVarList();
    Assert(vl.singleton());
    Variable v = vl.getHead();

    Node input = proofVariableToReason(v);
    if(input.getKind() == kind::AND){
      for(Node::iterator input_iter = input.begin(), input_end = input.end(); input_iter != input_end; ++input_iter){
	Node inputChild = *input_iter;
	nb << inputChild;
      }
    }else{
      nb << input;
    }
  }

  Node result = (nb.getNumChildren() == 1) ? nb[0] : (Node)nb;
  Debug("arith::dio") << "Proof at " << i << " is "
                      << d_trail[i].d_eq.getNode() << endl
                      << d_trail[i].d_proof.getNode() << endl
                      << " which becomes " << result << endl;
  return result;
}

bool DioSolver::anyCoefficientExceedsMaximum(TrailIndex j) const{
  uint32_t length = d_trail[j].d_eq.maxLength();
  uint32_t nmonos = d_trail[j].d_eq.getPolynomial().numMonomials();

  bool result =
    nmonos >= 2 &&
    length > d_maxInputCoefficientLength + MAX_GROWTH_RATE;
  if(Debug.isOn("arith::dio::max") && result){
    Debug("arith::dio::max") << "about to drop:";
    debugPrintTrail(j);
  }
  return result;
}

void DioSolver::enqueueInputConstraints(){

  TimerStat::CodeTimer codeTimer(d_statistics.d_enqueueInputConstraintsTimer);

  Assert(d_currentF.empty());
  while(d_savedQueueIndex < d_savedQueue.size()){
    d_currentF.push_back(d_savedQueue[d_savedQueueIndex]);
    d_savedQueueIndex = d_savedQueueIndex + 1;
  }

  while(d_nextInputConstraintToEnqueue < d_inputConstraints.size()  && !inConflict()){
    size_t curr = d_nextInputConstraintToEnqueue;
    d_nextInputConstraintToEnqueue = d_nextInputConstraintToEnqueue + 1;

    TrailIndex i = d_inputConstraints[curr].d_trailPos;
    TrailIndex j = _applyAllSubstitutionsToIndex(i);

    if(!triviallySat(j)){
      if(triviallyUnsat(j)){
        raiseConflict(j);
      }else{
        TrailIndex k = reduceByGCD(j);

        if(!inConflict()){
          if(triviallyUnsat(k)){
            raiseConflict(k);
          }else if(!(triviallySat(k) || anyCoefficientExceedsMaximum(k))){
            if(options::oldDio()){
              pushToQueueBack(k);
            }else{
              if(canDirectlySolve(k)){
                // directly solve if the index now if possible
                solveIndex(k);
              }else{
                pushToQueueBack(k);
              }
            }
          }
        }
      }
    }
  }
}


/*TODO Currently linear in the size of the Queue
 *It is not clear if am O(log n) strategy would be better.
 *Right before this in the algorithm is a substitution which could potentially
 *effect the key values of everything in the queue.
 */
void DioSolver::moveMinimumByAbsToQueueFront(){
  Assert(!queueEmpty());
  TimerStat::CodeTimer codeTimer(d_statistics.d_moveMinimumByAbsToQueueFrontTimer);

  //Select the minimum element.
  size_t indexInQueue = 0;
  Monomial minMonomial = d_trail[d_currentF[indexInQueue]].d_minimalMonomial;

  size_t N = d_currentF.size();
  for(size_t i=1; i < N; ++i){
    Monomial curr = d_trail[d_currentF[i]].d_minimalMonomial;
    if(curr.absCmp(minMonomial) < 0){
      indexInQueue = i;
      minMonomial = curr;
    }
  }

  TrailIndex tmp = d_currentF[indexInQueue];
  d_currentF[indexInQueue] = d_currentF.front();
  d_currentF.front() = tmp;
}

bool DioSolver::queueEmpty() const{
  return d_currentF.empty();
}

Node DioSolver::columnGcdIsOne() const{
  TimerStat::CodeTimer codeTimer((TimerStat&)d_statistics.d_columnGcdIsOneTimer);

  std::hash_map<Node, Integer, NodeHashFunction> gcdMap;

  std::deque<TrailIndex>::const_iterator iter, end;
  for(iter = d_currentF.begin(), end = d_currentF.end(); iter != end; ++iter){
    TrailIndex curr = *iter;
    Polynomial p = d_trail[curr].d_eq.getPolynomial();
    Polynomial::iterator monoIter = p.begin(), monoEnd = p.end();
    for(; monoIter != monoEnd; ++monoIter){
      Monomial m = *monoIter;
      VarList vl = m.getVarList();
      Node vlNode = vl.getNode();

      Constant c = m.getConstant();
      Integer zc = c.getValue().getNumerator();
      if(gcdMap.find(vlNode) == gcdMap.end()){
        // have not seen vl yet.
        // gcd is c
        Assert(c.isIntegral());
        Assert(!m.absCoefficientIsOne());
        gcdMap.insert(make_pair(vlNode, zc.abs()));
      }else{
        const Integer& currentGcd = gcdMap[vlNode];
        Integer newGcd = currentGcd.gcd(zc);
        if(newGcd == 1){
          return vlNode;
        }else{
          gcdMap[vlNode] = newGcd;
        }
      }
    }
  }
  return Node::null();
}

void DioSolver::saveQueue(){
  std::deque<TrailIndex>::const_iterator iter, end;
  for(iter = d_currentF.begin(), end = d_currentF.end(); iter != end; ++iter){
    d_savedQueue.push_back(*iter);
  }
}

DioSolver::TrailIndex DioSolver::impliedGcdOfOne(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_impliedGcdOfOneTimer);

  Node canReduce = columnGcdIsOne();
  if(canReduce.isNull()){
    return 0;
  }else{
    VarList vl = VarList::parseVarList(canReduce);

    TrailIndex current;
    Integer currentCoeff, currentGcd;

    //step 1 find the first equation containing vl
    //Set current and currentCoefficient
    std::deque<TrailIndex>::const_iterator iter, end;
    for(iter = d_currentF.begin(), end = d_currentF.end(); true; ++iter){
      Assert(iter != end);
      current = *iter;
      Constant coeff = d_trail[current].d_eq.getPolynomial().getCoefficient(vl);
      if(!coeff.isZero()){
        currentCoeff = coeff.getValue().getNumerator();
        currentGcd = currentCoeff.abs();

        ++iter;
        break;
      }
    }

    //For the rest of the equations keep reducing until the coefficient is one
    for(; iter != end; ++iter){
      Debug("arith::dio") << "next round : " << currentCoeff << " " << currentGcd << endl;
      TrailIndex inQueue = *iter;
      Constant iqc = d_trail[inQueue].d_eq.getPolynomial().getCoefficient(vl);
      if(!iqc.isZero()){
        Integer inQueueCoeff = iqc.getValue().getNumerator();

        //mpz_gcdext (mpz_t g, mpz_t s, mpz_t t, mpz_t a, mpz_t b);
        Integer g, s, t;
        // g = a*s + b*t
        Integer::extendedGcd(g, s, t, currentCoeff, inQueueCoeff);

        Debug("arith::dio") << "extendedReduction : " << endl;
        Debug("arith::dio") << g << " = " << s <<"*"<< currentCoeff << " + " << t <<"*"<< inQueueCoeff << endl;

        Assert(g <= currentGcd);
        if(g < currentGcd){
          if(s.sgn() == 0){
            Debug("arith::dio") << "extendedReduction drop" << endl;
            Assert(inQueueCoeff.divides(currentGcd));
            current = *iter;
            currentCoeff = inQueueCoeff;
            currentGcd = inQueueCoeff.abs();
          }else{

            Debug("arith::dio") << "extendedReduction combine" << endl;
            TrailIndex next = combineEqAtIndexes(current, s, inQueue, t);

            Assert(d_trail[next].d_eq.getPolynomial().getCoefficient(vl).getValue().getNumerator() == g);

            current = next;
            currentCoeff = g;
            currentGcd = g;
            if(currentGcd == 1){
              return current;
            }
          }
        }
      }
    }
    //This is not reachble as it is assured that the gcd of the column is 1
    Unreachable();
  }
}

bool DioSolver::canDirectlySolve(TrailIndex ti) const{
  Assert(!debugAnySubstitionApplies(ti));
  return d_trail[ti].d_minimalMonomial.absCoefficientIsOne();
}

bool DioSolver::processEquations(){
  Assert(!inConflict());


  enqueueInputConstraints();
  while(! queueEmpty() && !inConflict()){

    if(options::oldDio()){
      moveMinimumByAbsToQueueFront();

      TrailIndex minimum = d_currentF.front();
      TrailIndex reduceIndex;

      Assert(inRange(minimum));
      Assert(!inConflict());

      Debug("arith::dio") << "processEquations " << minimum << " : " << d_trail[minimum].d_eq.getNode() << endl;

      Assert(queueConditions(minimum));

      bool canDirectlySolve = d_trail[minimum].d_minimalMonomial.absCoefficientIsOne();

      std::pair<SubIndex, TrailIndex> p;
      if(canDirectlySolve){
        d_currentF.pop_front();
        p = solveIndex(minimum);
        reduceIndex = minimum;
      }else{
        TrailIndex implied = impliedGcdOfOne();

        if(implied != 0){
          p = solveIndex(implied);
          reduceIndex = implied;
        }else{
          d_currentF.pop_front();
          p = decomposeIndex(minimum);
          reduceIndex = minimum;
        }
      }

      SubIndex subIndex = p.first;
      TrailIndex next = p.second;
      subAndReduceCurrentFByIndex(subIndex);

      if(next != reduceIndex){
        if(triviallyUnsat(next)){
          raiseConflict(next);
        }else if(! triviallySat(next) ){
          pushToQueueBack(next);
        }
      }

    }else{
      moveMinimumByAbsToQueueFront();
      TrailIndex minimum = d_currentF.front();

      Assert(inRange(minimum));
      Assert(!inConflict());

      Debug("arith::dio") << "processEquations " << minimum
                          << " : " << d_trail[minimum].d_eq.getNode()
                          << endl;

      TrailIndex reducedMinimum = _applyAllSubstitutionsToIndex(minimum);

      Assert(!debugAnySubstitionApplies(reducedMinimum));

      Debug("arith::dio") << "processEquations " << reducedMinimum
                          << " : " << d_trail[reducedMinimum].d_eq.getNode()
                          << endl;

      if(triviallySat(reducedMinimum)){
        d_currentF.pop_front();
      }else if(triviallyUnsat(reducedMinimum)){
        raiseConflict(reducedMinimum);
      }else{
        TrailIndex k = reduceByGCD(reducedMinimum);
        if(inConflict()){
          break;
        }
        Assert(!triviallyUnsat(k));
        Assert(!triviallySat(k));
        Assert(queueConditions(k));
        d_currentF.pop_front();
        if(canDirectlySolve(k)){
          solveIndex(k);
        }else{
          std::pair<DioSolver::SubIndex, DioSolver::TrailIndex> p;
          p = decomposeIndex(reducedMinimum);
          TrailIndex next = p.second;
          if(triviallyUnsat(next)){
            raiseConflict(next);
            Assert(inConflict());
            break;
          }else if(! triviallySat(next) ){
            pushToQueueBack(next);
          }
        }
      }
    }
  }

  d_currentF.clear();
  return inConflict();
}

Node DioSolver::processEquationsForConflict(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_conflictTimer);
  ++(d_statistics.d_conflictCalls);

  Assert(!inConflict());
  if(processEquations()){
    ++(d_statistics.d_conflicts);
    return proveIndex(getConflictIndex());
  }else{
    return Node::null();
  }
}

SumPair DioSolver::processEquationsForCut(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_cutTimer);
  ++(d_statistics.d_cutCalls);

  Assert(!inConflict());
  if(processEquations()){
    ++(d_statistics.d_cuts);
    return purifyIndex(getConflictIndex());
  }else{
    return SumPair::mkZero();
  }
}

void DioSolver::generatePrimesUpTo(uint32_t N){
  d_smallPrimes = new std::vector<Integer>();
  d_smallPrimes->push_back(2);
  d_smallPrimes->push_back(3);
  d_smallPrimes->push_back(5);
  // 0 mod 6 cannot be prime
  // 1 mod 6
  // 2 mod 6 cannot be prime
  // 3 mod 6 cannot be prime
  // 4 mod 6 cannot be prime
  // 5 mod 6
  for(uint32_t i = 6; i <= N; i+=6){
    Integer j( i+1 );
    Integer k (i+5);

    bool failedJ = i + 1 > N;
    bool failedK = i + 1 > N;

    for(size_t ind = 0; !(failedJ && failedK) && ind < d_smallPrimes->size(); ++ind){
      const Integer& p = (*d_smallPrimes)[ind];
      if(!failedJ){
        if(p.divides(j)){
          failedJ = true;
        }
      }
      if(!failedK){
        if(p.divides(k)){
          failedK = true;
        }
      }
    }
    if(!failedK){
      d_smallPrimes->push_back(k);
    }
    if(!failedJ){
      d_smallPrimes->push_back(j);
    }
  }
}

Integer DioSolver::heuristicFindFactor(const Integer& x){
  if(x.isOne()){
    return x;
  }else if(x.isZero()){
    return Integer(1);
  }else{
    if(d_smallPrimes == NULL){
      generatePrimesUpTo(1000);
      Assert(d_smallPrimes != NULL);
    }
    const std::vector<Integer>& smallPrimes = *d_smallPrimes;

    for(size_t i=0, N = smallPrimes.size(); i < N; ++i){
      const Integer& p = smallPrimes[i];
      if(p.divides(x)){
        return p;
      }
    }
    return x;
  }
}

SumPair DioSolver::purifyIndex(TrailIndex i){
  // TODO: "This uses the substitution trail to reverse the substitutions from the sum term. Using the proof term should be more efficient."

  if(options::oldDio()){

    SumPair curr = d_trail[i].d_eq;

    Constant negOne = Constant::mkConstant(-1);

    for(uint32_t revIter = d_subs.size(); revIter > 0; --revIter){
      uint32_t i = revIter - 1;
      Node freshNode = d_subs[i].d_fresh;
      if(freshNode.isNull()){
        continue;
      }else{
        Variable var(freshNode);
        Polynomial vsum = curr.getPolynomial();

        Constant a = vsum.getCoefficient(VarList(var));
        if(!a.isZero()){
          const SumPair& sj = d_trail[d_subs[i].d_constraint].d_eq;
          Assert(sj.getPolynomial().getCoefficient(VarList(var)).isOne());
          SumPair newSi = (curr * negOne) + (sj * a);
          Assert(newSi.getPolynomial().getCoefficient(VarList(var)).isZero());
          curr = newSi;
        }
      }
    }
    return curr;
  }else{
    const SumPair& curr = d_trail[i].d_eq;
    const Polynomial& proof = d_trail[i].d_proof;

    TrailIndex trailSize = d_trail.size();
    TrailIndex multVar = trailSize;
    size_t sizeAtMultVar = 0;

    SumPair newConstraint(Polynomial::mkZero(),Constant::mkConstant(0));

    Polynomial::iterator iter = proof.begin(), end = proof.end();
    for(; iter!= end; ++iter){
      Monomial m = *iter;
      const Constant& c = m.getConstant();
      Node var = m.getVarList().getNode();

      Assert(d_varToInputConstraintMap.find(var) != d_varToInputConstraintMap.end());
      InputConstraintIndex ici = (*d_varToInputConstraintMap.find(var)).second;
      TrailIndex ti = d_inputConstraints[ici].d_trailPos;
      SumPair inp = d_trail[ti].d_eq;
      newConstraint = newConstraint + inp * c;

      size_t currSize = inp.getPolynomial().size();
      if(currSize >= 2){
        if(multVar == trailSize){
          multVar = ti;
          sizeAtMultVar = currSize;
        }else if(currSize < sizeAtMultVar){
          multVar = ti;
          sizeAtMultVar = currSize;
        }
      }
    }
    Polynomial lhs = newConstraint.getPolynomial();
    Assert(!lhs.isConstant());
    Constant rhs = curr.getConstant();
    Assert(rhs.isIntegral());

    if(lhs.size() == 1){
      d_singleVarCutsInARow++;
    }else{
      d_singleVarCutsInARow = 0;
    }

    if(options::massageCut() && d_singleVarCutsInARow >= 10 && multVar != trailSize){
      Integer g = lhs.gcd();
      Integer r = rhs.getValue().getNumerator();
      Assert(!g.divides(r));
      Assert(g.sgn() > 0);

      Integer d = g.gcd(r);
      Polynomial rlhs = lhs.exactDivide(d);
      Integer rrhs = r.exactQuotient(d);

      Integer dprime = heuristicFindFactor(d);

      SumPair inp = d_trail[multVar].d_eq;
      SumPair next = newConstraint + inp * Constant::mkConstant(Rational(dprime));
      newConstraint = next;
      d_singleVarCutsInARow = 0;
    }
    return newConstraint;
  }
  // Integer g = lhs.gcd();
  // Assert(!g.divides(c.getValue().getNumerator()));
  // Assert(g.sgn() > 0);

  // Integer d = g.gcd(c);
  // Polynomial rlhs = lhs.exactDivide(d);
  // Integer rrhs = (c.getValue().getNumerator()).exactQuotient(d);

  // Integer dprime = heuristicReduceDenom(d);

  // Constant negOne = Constant::mkConstant(-1);

  // for(uint32_t revIter = d_subs.size(); revIter > 0; --revIter){
  //   uint32_t i = revIter - 1;
  //   Node freshNode = d_subs[i].d_fresh;
  //   if(freshNode.isNull()){
  //     continue;
  //   }else{
  //     Variable var(freshNode);
  //     Polynomial vsum = curr.getPolynomial();

  //     Constant a = vsum.getCoefficient(VarList(var));
  //     if(!a.isZero()){
  //       const SumPair& sj = d_trail[d_subs[i].d_constraint].d_eq;
  //       Assert(sj.getPolynomial().getCoefficient(VarList(var)).isOne());
  //       SumPair newSi = (curr * negOne) + (sj * a);
  //       Assert(newSi.getPolynomial().getCoefficient(VarList(var)).isZero());
  //       curr = newSi;
  //     }
  //   }
  // }
  // return curr;
}

DioSolver::TrailIndex DioSolver::combineEqAtIndexes(DioSolver::TrailIndex i, const Integer& q, DioSolver::TrailIndex j, const Integer& r){
  Constant cq = Constant::mkConstant(q);
  Constant cr = Constant::mkConstant(r);

  const SumPair& si = d_trail[i].d_eq;
  const SumPair& sj = d_trail[j].d_eq;

  Debug("arith::dio") << "combineEqAtIndexes(" << i <<","<<q<<","<<j<<","<<r<<")"<<endl;
  Debug("arith::dio") << "d_facts[i] = " << si.getNode() << endl
                      << "d_facts[j] = " << sj.getNode() << endl;


  SumPair newSi = (si * cq) + (sj * cr);


  const Polynomial& pi = d_trail[i].d_proof;
  const Polynomial& pj = d_trail[j].d_proof;
  Polynomial newPi = (pi * cq) + (pj * cr);

  TrailIndex k = d_trail.size();
  d_trail.push_back(Constraint(newSi, newPi));


  Debug("arith::dio") << "derived "<< newSi.getNode()
                      <<" with proof " << newPi.getNode() << endl;

  return k;

}

void DioSolver::printQueue(){
  Debug("arith::dio") << "DioSolver::printQueue()" << endl;
  for(TrailIndex i = 0, last = d_trail.size(); i < last; ++i){
    Debug("arith::dio") << "d_trail[i].d_eq = " << d_trail[i].d_eq.getNode() << endl;
    Debug("arith::dio") << "d_trail[i].d_proof = " << d_trail[i].d_proof.getNode() << endl;
  }

  Debug("arith::dio") << "DioSolver::printSubs()" << endl;
  for(SubIndex si=0, sN=d_subs.size(); si < sN; ++si){
    Debug("arith::dio") << "d_subs[i] = {"
                        << "d_fresh="<< d_subs[si].d_fresh <<","
                        << "d_eliminated="<< d_subs[si].d_eliminated.getNode() <<","
                        << "d_constraint="<< d_subs[si].d_constraint <<"}" << endl;
    Debug("arith::dio") << "d_trail[d_subs[i].d_constraint].d_eq="
                        << d_trail[d_subs[si].d_constraint].d_eq.getNode() << endl;
  }
}

DioSolver::TrailIndex DioSolver::_applyAllSubstitutionsToIndex(DioSolver::TrailIndex trailIndex){
  TrailIndex currentIndex = trailIndex;
  bool appliedSub;
  do{
    appliedSub = false;

    const SumPair& curr = d_trail[currentIndex].d_eq;
    Polynomial csum = curr.getPolynomial();

    SubIndex subSelected = d_subs.size();
    Polynomial::iterator iter = csum.begin(), end = csum.end();
    for(; iter!= end; ++iter){
      Monomial m = *iter;
      VarList vl = m.getVarList();
      if(d_elimPos.contains(vl.getNode())){
        SubIndex subCurr = d_elimPos[vl.getNode()];
        if(subCurr < subSelected){
          subSelected = subCurr;
        }
      }
    }
    if(subSelected < d_subs.size()){
      TrailIndex nextIndex = _applySubstitution(subSelected, currentIndex);
      Assert(nextIndex != currentIndex);
      currentIndex = nextIndex;
      appliedSub = true;
    }
  }while(appliedSub);

  Assert(!debugAnySubstitionApplies(currentIndex));
  return currentIndex;
}

bool DioSolver::debugSubstitutionApplies(DioSolver::SubIndex si, DioSolver::TrailIndex ti) const {
  Variable var = d_subs[si].d_eliminated;

  const SumPair& curr = d_trail[ti].d_eq;
  Polynomial vsum = curr.getPolynomial();

  Constant a = vsum.getCoefficient(VarList(var));
  return !a.isZero();
}

bool DioSolver::debugAnySubstitionApplies(DioSolver::TrailIndex i) const{
  for(SubIndex subIter = 0, siEnd = d_subs.size(); subIter < siEnd; ++subIter){
    if(debugSubstitutionApplies(subIter, i)){
      return true;
    }
  }
  return false;
}

std::pair<DioSolver::SubIndex, DioSolver::TrailIndex> DioSolver::solveIndex(DioSolver::TrailIndex i){
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveIndexTimer);
  Assert(!debugAnySubstitionApplies(i));


  const SumPair& si = d_trail[i].d_eq;

  Debug("arith::dio") << "before solveIndex("<<i<<":"<<si.getNode()<< ")" << endl;

#ifdef CVC4_ASSERTIONS
  const Polynomial& p = si.getPolynomial();
#endif

  Assert(p.isIntegral());

  Assert(p.selectAbsMinimum() == d_trail[i].d_minimalMonomial);
  const Monomial av = d_trail[i].d_minimalMonomial;

  VarList vl = av.getVarList();
  Assert(vl.singleton());
  Variable var = vl.getHead();
  Constant a = av.getConstant();
  Integer a_abs = a.getValue().getNumerator().abs();

  Assert(a_abs == 1);

  TrailIndex ci = !a.isNegative() ? scaleEqAtIndex(i, Integer(-1)) : i;

  SubIndex subBy = push_back_sub(Node::null(), var, ci);

  Debug("arith::dio") << "solveIndex " <<  d_trail[ci].d_eq.getNode() << " for " << av.getNode() << endl;
  Assert(d_trail[ci].d_eq.getPolynomial().getCoefficient(vl) == Constant::mkConstant(-1));

  return make_pair(subBy, i);
}

std::pair<DioSolver::SubIndex, DioSolver::TrailIndex> DioSolver::decomposeIndex(DioSolver::TrailIndex i){
  const SumPair& si = d_trail[i].d_eq;

  d_usedDecomposeIndex = true;
  Assert(!debugAnySubstitionApplies(i));
  Debug("arith::dio") << "before decomposeIndex("<<i<<":"<<si.getNode()<< ")" << endl;

#ifdef CVC4_ASSERTIONS
  const Polynomial& p = si.getPolynomial();
#endif

  Assert(p.isIntegral());

  Assert(p.selectAbsMinimum() == d_trail[i].d_minimalMonomial);
  const Monomial& av = d_trail[i].d_minimalMonomial;

  VarList vl = av.getVarList();
  Assert(vl.singleton());
  Variable var = vl.getHead();
  Constant a = av.getConstant();
  Integer a_abs = a.getValue().getNumerator().abs();

  Assert(a_abs > 1);

  //It is not sufficient to reduce the case where abs(a) == 1 to abs(a) > 1.
  //We need to handle both cases seperately to ensure termination.
  Node qr = SumPair::computeQR(si, a.getValue().getNumerator());

  Assert(qr.getKind() == kind::PLUS);
  Assert(qr.getNumChildren() == 2);
  SumPair q = SumPair::parseSumPair(qr[0]);
  SumPair r = SumPair::parseSumPair(qr[1]);

  Assert(q.getPolynomial().getCoefficient(vl) == Constant::mkConstant(1));

  Assert(!r.isZero());
  Node freshNode = makeIntegerVariable();
  Variable fresh(freshNode);
  SumPair fresh_one=SumPair::mkSumPair(fresh);
  SumPair fresh_a = fresh_one * a;

  SumPair newSI = SumPair(fresh_one) - q;
  // this normalizes the coefficient of var to -1


  TrailIndex ci = d_trail.size();
  d_trail.push_back(Constraint(newSI, Polynomial::mkZero()));
  // no longer reference av safely!
  addTrailElementAsLemma(ci);

  Debug("arith::dio") << "Decompose ci(" << ci <<":" <<  d_trail[ci].d_eq.getNode()
                      << ") for " << d_trail[i].d_minimalMonomial.getNode() << endl;
  Assert(d_trail[ci].d_eq.getPolynomial().getCoefficient(vl) == Constant::mkConstant(-1));
  SumPair newFact = r + fresh_a;

  TrailIndex nextIndex = d_trail.size();
  d_trail.push_back(Constraint(newFact, d_trail[i].d_proof));

  SubIndex subBy = push_back_sub(freshNode, var, ci);

  Debug("arith::dio") << "Decompose nextIndex " <<  d_trail[nextIndex].d_eq.getNode() << endl;
  return make_pair(subBy, nextIndex);
}

bool DioSolver::debugIsZeroOn(TrailIndex ti, const Variable& v) const {
  Polynomial atTi = d_trail[ti].d_eq.getPolynomial();
  return atTi.getCoefficient(VarList(v)).isZero();
}

DioSolver::TrailIndex DioSolver::_applySubstitution(DioSolver::SubIndex si, DioSolver::TrailIndex ti){
  Variable var = d_subs[si].d_eliminated;
  TrailIndex subIndex = d_subs[si].d_constraint;

  const SumPair& curr = d_trail[ti].d_eq;
  Polynomial vsum = curr.getPolynomial();

  Constant a = vsum.getCoefficient(VarList(var));
  Assert(a.isIntegral());
  Assert(!a.isZero());

  Integer one(1);
  TrailIndex afterSub = combineEqAtIndexes(ti, one, subIndex, a.getValue().getNumerator());
  Assert(debugIsZeroOn(afterSub, var));
  Assert(afterSub != ti);
  return afterSub;
}


DioSolver::TrailIndex DioSolver::reduceByGCD(DioSolver::TrailIndex ti){

  const SumPair& sp = d_trail[ti].d_eq;
  Polynomial vsum = sp.getPolynomial();
  Constant c = sp.getConstant();

  Debug("arith::dio") << "reduceByGCD " << vsum.getNode() << endl;
  Assert(!vsum.isConstant());
  Integer g = vsum.gcd();
  Assert(g >= 1);
  Debug("arith::dio") << "gcd("<< vsum.getNode() <<")=" << g << " " << c.getValue() << endl;
  if(g.divides(c.getValue().getNumerator())){
    if(g > 1){
      return scaleEqAtIndex(ti, g);
    }else{
      return ti;
    }
  }else{
    raiseConflict(ti);
    return ti;
  }
}

bool DioSolver::triviallySat(TrailIndex i){
  const SumPair& eq = d_trail[i].d_eq;
  if(eq.isConstant()){
    return eq.getConstant().isZero();
  }else{
    return false;
  }
}

bool DioSolver::triviallyUnsat(DioSolver::TrailIndex i){
  const SumPair& eq = d_trail[i].d_eq;
  if(eq.isConstant()){
    return !eq.getConstant().isZero();
  }else{
    return false;
  }
}


bool DioSolver::gcdIsOne(DioSolver::TrailIndex i){
  const SumPair& eq = d_trail[i].d_eq;
  return eq.gcd() == Integer(1);
}

void DioSolver::debugPrintTrail(DioSolver::TrailIndex i) const{
  const SumPair& eq = d_trail[i].d_eq;
  const Polynomial& proof = d_trail[i].d_proof;

  Message() << "d_trail["<<i<<"].d_eq = " << eq.getNode() << endl;
  Message() << "d_trail["<<i<<"].d_proof = " << proof.getNode() << endl;
}

void DioSolver::subAndReduceCurrentFByIndex(DioSolver::SubIndex subIndex){
  TimerStat::CodeTimer codeTimer(d_statistics.d_subAndReduceCurrentFByIndexTimer);
  size_t N = d_currentF.size();

  size_t readIter = 0, writeIter = 0;
  for(; readIter < N && !inConflict(); ++readIter){
    TrailIndex curr = d_currentF[readIter];
    TrailIndex nextTI = _applySubstitution(subIndex, curr);
    if(nextTI == curr){
      d_currentF[writeIter] = curr;
      ++writeIter;
    }else{
      Assert(nextTI != curr);

      if(triviallyUnsat(nextTI)){
        raiseConflict(nextTI);
      }else if(!triviallySat(nextTI)){
        TrailIndex nextNextTI = reduceByGCD(nextTI);

        if(!(inConflict() || anyCoefficientExceedsMaximum(nextNextTI))){
          Assert(queueConditions(nextNextTI));
          d_currentF[writeIter] = nextNextTI;
          ++writeIter;
        }
      }
    }
  }
  if(!inConflict() && writeIter < N){
    d_currentF.resize(writeIter);
  }
}

void DioSolver::addTrailElementAsLemma(TrailIndex i) {
  if(options::exportDioDecompositions()){
    d_decompositionLemmaQueue.push(i);
  }
}

Node DioSolver::trailIndexToEquality(TrailIndex i) const {
  const SumPair& sp = d_trail[i].d_eq;
  Node zero = mkRationalNode(0);
  Node eq = (sp.getNode()).eqNode(zero);
  return eq;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
