/*********************                                                        */
/*! \file linear_equality.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This implements the LinearEqualityModule.
 **
 ** This implements the LinearEqualityModule.
 **/


#include "theory/arith/linear_equality.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

/* Explicitly instatiate these functions. */
template void LinearEqualityModule::propagateNonbasics<true>(ArithVar basic, Constraint c);
template void LinearEqualityModule::propagateNonbasics<false>(ArithVar basic, Constraint c);

template ArithVar LinearEqualityModule::selectSlack<true>(ArithVar x_i, PreferenceFunction pf) const;
template ArithVar LinearEqualityModule::selectSlack<false>(ArithVar x_i, PreferenceFunction pf) const;

LinearEqualityModule::LinearEqualityModule(ArithVariables& vars, Tableau& t, BasicVarModelUpdateCallBack f):
  d_variables(vars),
  d_tableau(t),
  d_basicVariableUpdates(f),
  d_trackCallback(this)
{}

LinearEqualityModule::Statistics::Statistics():
  d_statPivots("theory::arith::pivots",0),
  d_statUpdates("theory::arith::updates",0),
  d_pivotTime("theory::arith::pivotTime"),
  d_weakeningAttempts("theory::arith::weakening::attempts",0),
  d_weakeningSuccesses("theory::arith::weakening::success",0),
  d_weakenings("theory::arith::weakening::total",0),
  d_weakenTime("theory::arith::weakening::time")
{
  StatisticsRegistry::registerStat(&d_statPivots);
  StatisticsRegistry::registerStat(&d_statUpdates);

  StatisticsRegistry::registerStat(&d_pivotTime);

  StatisticsRegistry::registerStat(&d_weakeningAttempts);
  StatisticsRegistry::registerStat(&d_weakeningSuccesses);
  StatisticsRegistry::registerStat(&d_weakenings);
  StatisticsRegistry::registerStat(&d_weakenTime);
}

LinearEqualityModule::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statPivots);
  StatisticsRegistry::unregisterStat(&d_statUpdates);
  StatisticsRegistry::unregisterStat(&d_pivotTime);


  StatisticsRegistry::unregisterStat(&d_weakeningAttempts);
  StatisticsRegistry::unregisterStat(&d_weakeningSuccesses);
  StatisticsRegistry::unregisterStat(&d_weakenings);
  StatisticsRegistry::unregisterStat(&d_weakenTime);
}

void LinearEqualityModule::update(ArithVar x_i, const DeltaRational& v){
  Assert(!d_tableau.isBasic(x_i));
  const DeltaRational& assignment_x_i = d_variables.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);

  if(d_areTracking){
    Unimplemented();
  }

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  Tableau::ColIterator basicIter = d_tableau.colIterator(x_i);
  for(; !basicIter.atEnd(); ++basicIter){
    const Tableau::Entry& entry = *basicIter;
    Assert(entry.getColVar() == x_i);

    ArithVar x_j = d_tableau.rowIndexToBasic(entry.getRowIndex());
    const Rational& a_ji = entry.getCoefficient();

    const DeltaRational& assignment = d_variables.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    d_variables.setAssignment(x_j, nAssignment);

    d_basicVariableUpdates(x_j);
  }

  d_variables.setAssignment(x_i, v);

  //double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowLength(x_i));

  //(d_statistics.d_avgNumRowsNotContainingOnUpdate).addEntry(difference);
  if(Debug.isOn("paranoid:check_tableau")){  debugCheckTableau(); }
}

void LinearEqualityModule::pivotAndUpdate(ArithVar x_i, ArithVar x_j, const DeltaRational& v){
  Assert(x_i != x_j);

  TimerStat::CodeTimer codeTimer(d_statistics.d_pivotTime);

  static int instance = 0;

  if(Debug.isOn("arith::tracking::pre")){
    ++instance;
    Debug("arith::tracking")  << "pre update #" << instance << endl;
    debugCheckTracking();
  }

  if(Debug.isOn("arith::simplex:row")){ debugPivot(x_i, x_j); }

  RowIndex ridx = d_tableau.basicToRowIndex(x_i);
  const Tableau::Entry& entry_ij =  d_tableau.findEntry(ridx, x_j);
  Assert(!entry_ij.blank());


  const Rational& a_ij = entry_ij.getCoefficient();


  const DeltaRational& betaX_i = d_variables.getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;
  d_variables.setAssignment(x_i, v);

  Assert(inv_aij.sgn() != 0);

  Assert(d_areTracking);
  BoundCounts bc_i = countBounds(x_i);
  BoundCounts before = (d_variables.boundCounts(x_j));

  DeltaRational tmp = d_variables.getAssignment(x_j) + theta;
  d_variables.setAssignment(x_j, tmp);

  BoundCounts after = (d_variables.boundCounts(x_j));
  
  BoundCounts next_bc_i = (bc_i - before.multiplyBySgn(a_ij.sgn()))
    + after.multiplyBySgn(a_ij.sgn());
  d_boundTracking.set(x_i, next_bc_i);

  //Assert(matchingSets(d_tableau, x_j));
  for(Tableau::ColIterator iter = d_tableau.colIterator(x_j); !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;
    Assert(entry.getColVar() == x_j);
    RowIndex currRow = entry.getRowIndex();
    if(ridx != currRow ){
      ArithVar x_k = d_tableau.rowIndexToBasic(currRow);
      const Rational& a_kj = entry.getCoefficient();
      DeltaRational nextAssignment = d_variables.getAssignment(x_k) + (theta * a_kj);
      d_variables.setAssignment(x_k, nextAssignment);

      if(basicIsTracked(x_k)){
        BoundCounts next_bc_k = d_boundTracking[x_k];
        next_bc_k -= before.multiplyBySgn(a_kj.sgn());
        next_bc_k += after.multiplyBySgn(a_kj.sgn());
        
        d_boundTracking.set(x_k, next_bc_k);
      }

      d_basicVariableUpdates(x_k);
    }
  }

  if(Debug.isOn("arith::tracking::mid")){
    Debug("arith::tracking")  << "postupdate prepivot #" << instance << endl;
    debugCheckTracking();
  }

  // Pivots
  ++(d_statistics.d_statPivots);

  d_tableau.pivot(x_i, x_j, d_trackCallback);

  if(Debug.isOn("arith::tracking::post")){
    Debug("arith::tracking")  << "postpivot #" << instance << endl;
    debugCheckTracking();
  }

  d_basicVariableUpdates(x_i);
  d_basicVariableUpdates(x_j);

  if(Debug.isOn("matrix")){
    d_tableau.printMatrix();
  }
}

void LinearEqualityModule::debugCheckTracking(){
  Tableau::BasicIterator basicIter = d_tableau.beginBasic(),
    endIter = d_tableau.endBasic();
  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    Debug("arith::tracking") << "arith::tracking row basic: " << basic << endl;

    for(Tableau::RowIterator iter = d_tableau.basicRowIterator(basic); !iter.atEnd() && Debug.isOn("arith::tracking"); ++iter){
      const Tableau::Entry& entry = *iter;

      ArithVar var = entry.getColVar();
      const Rational& coeff = entry.getCoefficient();
      DeltaRational beta = d_variables.getAssignment(var);
      Debug("arith::tracking") << var << " " << d_variables.boundCounts(var)
                               << " " << beta << coeff;
      if(d_variables.hasLowerBound(var)){
        Debug("arith::tracking") << "(lb " << d_variables.getLowerBound(var) << ")";
      }
      if(d_variables.hasUpperBound(var)){
        Debug("arith::tracking") << "(up " << d_variables.getUpperBound(var) << ")";
      }
      Debug("arith::tracking") << endl;
      
    }
    Debug("arith::tracking") << "end row"<< endl;

    if(basicIsTracked(basic)){
      BoundCounts computed = computeBoundCounts(basic);
      Debug("arith::tracking")
        << "computed " << computed
        << " tracking " << d_boundTracking[basic] << endl;
      Assert(computed == d_boundTracking[basic]);
      
    }
  }
}

void LinearEqualityModule::debugPivot(ArithVar x_i, ArithVar x_j){
  Debug("arith::pivot") << "debugPivot("<< x_i  <<"|->"<< x_j << ")" << endl;

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;

    ArithVar var = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    DeltaRational beta = d_variables.getAssignment(var);
    Debug("arith::pivot") << var << beta << coeff;
    if(d_variables.hasLowerBound(var)){
      Debug("arith::pivot") << "(lb " << d_variables.getLowerBound(var) << ")";
    }
    if(d_variables.hasUpperBound(var)){
      Debug("arith::pivot") << "(up " << d_variables.getUpperBound(var) << ")";
    }
    Debug("arith::pivot") << endl;
  }
  Debug("arith::pivot") << "end row"<< endl;
}

/**
 * This check is quite expensive.
 * It should be wrapped in a Debug.isOn() guard.
 *   if(Debug.isOn("paranoid:check_tableau")){
 *      checkTableau();
 *   }
 */
void LinearEqualityModule::debugCheckTableau(){
  Tableau::BasicIterator basicIter = d_tableau.beginBasic(),
    endIter = d_tableau.endBasic();
  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    Tableau::RowIterator nonbasicIter = d_tableau.basicRowIterator(basic);
    for(; !nonbasicIter.atEnd(); ++nonbasicIter){
      const Tableau::Entry& entry = *nonbasicIter;
      ArithVar nonbasic = entry.getColVar();
      if(basic == nonbasic) continue;

      const Rational& coeff = entry.getCoefficient();
      DeltaRational beta = d_variables.getAssignment(nonbasic);
      Debug("paranoid:check_tableau") << nonbasic << beta << coeff<<endl;
      sum = sum + (beta*coeff);
    }
    DeltaRational shouldBe = d_variables.getAssignment(basic);
    Debug("paranoid:check_tableau") << "ending row" << sum
                                    << "," << shouldBe << endl;

    Assert(sum == shouldBe);
  }
}
bool LinearEqualityModule::debugEntireLinEqIsConsistent(const string& s){
  bool result = true;
  for(ArithVar var = 0, end = d_tableau.getNumColumns(); var != end; ++var){
    //  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    //ArithVar var = d_arithvarNodeMap.asArithVar(*i);
    if(!d_variables.assignmentIsConsistent(var)){
      d_variables.printModel(var);
      Warning() << s << ":" << "Assignment is not consistent for " << var ;
      if(d_tableau.isBasic(var)){
        Warning() << " (basic)";
      }
      Warning() << endl;
      result = false;
    }
  }
  return result;
}

DeltaRational LinearEqualityModule::computeBound(ArithVar basic, bool upperBound){
  DeltaRational sum(0,0);
  for(Tableau::RowIterator i = d_tableau.basicRowIterator(basic); !i.atEnd(); ++i){
    const Tableau::Entry& entry = (*i);
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == basic) continue;
    const Rational& coeff =  entry.getCoefficient();
    int sgn = coeff.sgn();
    bool ub = upperBound ? (sgn > 0) : (sgn < 0);

    const DeltaRational& bound = ub ?
      d_variables.getUpperBound(nonbasic):
      d_variables.getLowerBound(nonbasic);

    DeltaRational diff = bound * coeff;
    sum = sum + diff;
  }
  return sum;
}

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational LinearEqualityModule::computeRowValue(ArithVar x, bool useSafe){
  Assert(d_tableau.isBasic(x));
  DeltaRational sum(0);

  for(Tableau::RowIterator i = d_tableau.basicRowIterator(x); !i.atEnd(); ++i){
    const Tableau::Entry& entry = (*i);
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x) continue;
    const Rational& coeff = entry.getCoefficient();

    const DeltaRational& assignment = d_variables.getAssignment(nonbasic, useSafe);
    sum = sum + (assignment * coeff);
  }
  return sum;
}

bool LinearEqualityModule::hasBounds(ArithVar basic, bool upperBound){
  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(basic); !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;

    ArithVar var = entry.getColVar();
    if(var == basic) continue;
    int sgn = entry.getCoefficient().sgn();
    if(upperBound){
      if( (sgn < 0 && !d_variables.hasLowerBound(var)) ||
          (sgn > 0 && !d_variables.hasUpperBound(var))){
        return false;
      }
    }else{
      if( (sgn < 0 && !d_variables.hasUpperBound(var)) ||
          (sgn > 0 && !d_variables.hasLowerBound(var))){
        return false;
      }
    }
  }
  return true;
}

template <bool upperBound>
void LinearEqualityModule::propagateNonbasics(ArithVar basic, Constraint c){
  Assert(d_tableau.isBasic(basic));
  Assert(c->getVariable() == basic);
  Assert(!c->assertedToTheTheory());
  //Assert(c->canBePropagated());
  Assert(!c->hasProof());

  Debug("arith::explainNonbasics") << "LinearEqualityModule::explainNonbasics("
                                   << basic <<") start" << endl;

  vector<Constraint> bounds;

  Tableau::RowIterator iter = d_tableau.basicRowIterator(basic);
  for(; !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == basic) continue;

    const Rational& a_ij = entry.getCoefficient();

    int sgn = a_ij.sgn();
    Assert(sgn != 0);
    Constraint bound = NullConstraint;
    if(upperBound){
      if(sgn < 0){
        bound = d_variables.getLowerBoundConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_variables.getUpperBoundConstraint(nonbasic);
      }
    }else{
      if(sgn < 0){
        bound = d_variables.getUpperBoundConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_variables.getLowerBoundConstraint(nonbasic);
      }
    }
    Assert(bound != NullConstraint);
    Debug("arith::explainNonbasics") << "explainNonbasics" << bound << " for " << c << endl;
    bounds.push_back(bound);
  }
  c->impliedBy(bounds);
  Debug("arith::explainNonbasics") << "LinearEqualityModule::explainNonbasics("
                                   << basic << ") done" << endl;
}

Constraint LinearEqualityModule::weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v, const Rational& coeff, bool& anyWeakening, ArithVar basic) const {

  int sgn = coeff.sgn();
  bool ub = aboveUpper?(sgn < 0) : (sgn > 0);

  Constraint c = ub ?
    d_variables.getUpperBoundConstraint(v) :
    d_variables.getLowerBoundConstraint(v);

  bool weakened;
  do{
    const DeltaRational& bound = c->getValue();

    weakened = false;

    Constraint weaker = ub?
      c->getStrictlyWeakerUpperBound(true, true):
      c->getStrictlyWeakerLowerBound(true, true);

    if(weaker != NullConstraint){
      const DeltaRational& weakerBound = weaker->getValue();

      DeltaRational diff = aboveUpper ? bound - weakerBound : weakerBound - bound;
      //if var == basic,
      //  if aboveUpper, weakerBound > bound, multiply by -1
      //  if !aboveUpper, weakerBound < bound, multiply by -1
      diff = diff * coeff;
      if(surplus > diff){
        ++d_statistics.d_weakenings;
        weakened = true;
        anyWeakening = true;
        surplus = surplus - diff;

        Debug("weak") << "found:" << endl;
        if(v == basic){
          Debug("weak") << "  basic: ";
        }
        Debug("weak") << "  " << surplus << " "<< diff  << endl
                      << "  " << bound << c << endl
                      << "  " << weakerBound << weaker << endl;

        Assert(diff.sgn() > 0);
        c = weaker;
      }
    }
  }while(weakened);

  return c;
}

Node LinearEqualityModule::minimallyWeakConflict(bool aboveUpper, ArithVar basicVar) const {
  TimerStat::CodeTimer codeTimer(d_statistics.d_weakenTime);

  const DeltaRational& assignment = d_variables.getAssignment(basicVar);
  DeltaRational surplus;
  if(aboveUpper){
    Assert(d_variables.hasUpperBound(basicVar));
    Assert(assignment > d_variables.getUpperBound(basicVar));
    surplus = assignment - d_variables.getUpperBound(basicVar);
  }else{
    Assert(d_variables.hasLowerBound(basicVar));
    Assert(assignment < d_variables.getLowerBound(basicVar));
    surplus = d_variables.getLowerBound(basicVar) - assignment;
  }

  NodeBuilder<> conflict(kind::AND);
  bool anyWeakenings = false;
  for(Tableau::RowIterator i = d_tableau.basicRowIterator(basicVar); !i.atEnd(); ++i){
    const Tableau::Entry& entry = *i;
    ArithVar v = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    bool weakening = false;
    Constraint c = weakestExplanation(aboveUpper, surplus, v, coeff, weakening, basicVar);
    Debug("weak") << "weak : " << weakening << " "
                  << c->assertedToTheTheory() << " "
                  << d_variables.getAssignment(v) << " "
                  << c << endl
                  << c->explainForConflict() << endl;
    anyWeakenings = anyWeakenings || weakening;

    Debug("weak") << "weak : " << c->explainForConflict() << endl;
    c->explainForConflict(conflict);
  }
  ++d_statistics.d_weakeningAttempts;
  if(anyWeakenings){
    ++d_statistics.d_weakeningSuccesses;
  }
  return conflict;
}

ArithVar LinearEqualityModule::minVarOrder(ArithVar x, ArithVar y) const {
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  if(x <= y){
    return x;
  } else {
    return y;
  }
}

ArithVar LinearEqualityModule::minColLength(ArithVar x, ArithVar y) const {
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!d_tableau.isBasic(x));
  Assert(!d_tableau.isBasic(y));
  uint32_t xLen = d_tableau.getColLength(x);
  uint32_t yLen = d_tableau.getColLength(y);
  if( xLen > yLen){
     return y;
  } else if( xLen== yLen ){
    return minVarOrder(x,y);
  }else{
    return x;
  }
}

ArithVar LinearEqualityModule::minBoundAndColLength(ArithVar x, ArithVar y) const{
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!d_tableau.isBasic(x));
  Assert(!d_tableau.isBasic(y));
  if(d_variables.hasEitherBound(x) && d_variables.hasEitherBound(y)){
    return y;
  }else if(d_variables.hasEitherBound(x) && d_variables.hasEitherBound(y)){
    return x;
  }else {
    return minColLength(x, y);
  }
}

template <bool above>
ArithVar LinearEqualityModule::selectSlack(ArithVar x_i, PreferenceFunction pref) const{
  ArithVar slack = ARITHVAR_SENTINEL;

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd();  ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = entry.getCoefficient();
    int sgn = a_ij.sgn();
    if(isAcceptableSlack<above>(sgn, nonbasic)){
      //If one of the above conditions is met, we have found an acceptable
      //nonbasic variable to pivot x_i with.  We can now choose which one we
      //prefer the most.
      slack = (slack == ARITHVAR_SENTINEL) ? nonbasic : (this->*pref)(slack, nonbasic);
    }
  }

  return slack;
}

void LinearEqualityModule::startTrackingBoundCounts(){
  Assert(!d_areTracking);
  Assert(d_boundTracking.empty());

  d_areTracking = true;
  Assert(d_areTracking);
}

void LinearEqualityModule::stopTrackingBoundCounts(){
  Assert(d_areTracking);
  d_boundTracking.purge();

  d_areTracking = false;
  Assert(!d_areTracking);
  Assert(d_boundTracking.empty());
}


BoundCounts LinearEqualityModule::computeBoundCounts(ArithVar x_i) const{
  BoundCounts counts(0,0);

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd();  ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = entry.getCoefficient();
    counts += (d_variables.boundCounts(nonbasic)).multiplyBySgn(a_ij.sgn());
  }

  return counts;
}

BoundCounts LinearEqualityModule::cachingCountBounds(ArithVar x_i) const{
  if(d_boundTracking.isKey(x_i)){
    return d_boundTracking[x_i];
  }else{
    return computeBoundCounts(x_i);
  }
}

BoundCounts LinearEqualityModule::countBounds(ArithVar x_i){
  if(d_boundTracking.isKey(x_i)){
    return d_boundTracking[x_i];
  }else{
    BoundCounts bc = computeBoundCounts(x_i);
    if(d_areTracking){
      d_boundTracking.set(x_i,bc);
    }
    return bc;
  }
}

bool LinearEqualityModule::nonbasicsAtLowerBounds(ArithVar x_i) const {
  BoundCounts bcs = cachingCountBounds(x_i);
  RowIndex ridx = d_tableau.basicToRowIndex(x_i);
  uint32_t length = d_tableau.getRowLength(ridx);

  return bcs.atLowerBounds() + 1 == length;
}

bool LinearEqualityModule::nonbasicsAtUpperBounds(ArithVar x_i) const {
  BoundCounts bcs = cachingCountBounds(x_i);
  RowIndex ridx = d_tableau.basicToRowIndex(x_i);
  uint32_t length = d_tableau.getRowLength(ridx);

  return bcs.atUpperBounds() + 1 == length;
}

void LinearEqualityModule::trackingFinishedRow(RowIndex ridx){
  ArithVar basic = d_tableau.rowIndexToBasic(ridx);
  if(basicIsTracked(basic)){
    uint32_t length = d_tableau.getRowLength(ridx);
    BoundCounts bcs = d_boundTracking[basic];
    if(bcs.atLowerBounds() + 1 == length ||
       bcs.atUpperBounds() + 1 == length){
      d_basicVariableUpdates(basic);
    }
  }
}

void LinearEqualityModule::trackingSwap(ArithVar basic, ArithVar nb, int nbSgn) {
  Assert(basicIsTracked(basic));

  // z = a*x + \sum b*y
  // x = (1/a) z + \sum (-1/a)*b*y
  // basicCount(z) = bc(a*x) +  bc(\sum b y)
  // basicCount(x) = bc(z/a) + bc(\sum -b/a * y)

  // sgn(1/a) = sgn(a)
  // bc(a*x) = bc(x).multiply(sgn(a))
  // bc(z/a) = bc(z).multiply(sgn(a))
  // bc(\sum -b/a * y) = bc(\sum b y).multiplyBySgn(-sgn(a))
  // bc(\sum b y) = basicCount(z) - bc(a*x)
  // basicCount(x) =
  //  = bc(z).multiply(sgn(a)) + (basicCount(z) - bc(a*x)).multiplyBySgn(-sgn(a))

  BoundCounts bc = d_boundTracking[basic];
  bc -= (d_variables.boundCounts(nb)).multiplyBySgn(nbSgn);
  bc = bc.multiplyBySgn(-nbSgn);
  bc += d_variables.boundCounts(basic).multiplyBySgn(nbSgn);
  d_boundTracking.set(nb, bc);
  d_boundTracking.remove(basic);
}

void LinearEqualityModule::trackingCoefficientChange(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn){
  ArithVar basic = d_tableau.rowIndexToBasic(ridx);
  if(basicIsTracked(basic)){
    BoundCounts nb_bc = d_variables.boundCounts(nb);
    BoundCounts basic_bc = d_boundTracking[basic];
    basic_bc -= nb_bc.multiplyBySgn(oldSgn);
    basic_bc += nb_bc.multiplyBySgn(currSgn);
    d_boundTracking.set(basic, basic_bc);
  }  
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
