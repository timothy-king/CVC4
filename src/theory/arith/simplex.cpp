/*********************                                                        */
/*! \file simplex.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/simplex.h"
#include "theory/arith/options.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

DualSimplexDecisionProcedure::DualSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
  , d_pivotsInRound()
  , d_statistics()
{ }

SimplexDecisionProcedure::SimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : d_conflictVariables()
  , d_linEq(linEq)
  , d_variables(d_linEq.getVariables())
  , d_tableau(d_linEq.getTableau())
  , d_errorSet(errors)
  , d_numVariables(0)
  , d_conflictChannel(conflictChannel)
  , d_arithVarMalloc(tvmalloc)
{
  d_heuristicRule = options::arithErrorSelectionRule();
  d_errorSet.setSelectionRule(d_heuristicRule);
}

DualSimplexDecisionProcedure::Statistics::Statistics():
  d_statUpdateConflicts("theory::arith::dual::UpdateConflicts", 0),
  d_processSignalsTime("theory::arith::dual::findConflictOnTheQueueTime"),
  d_simplexConflicts("theory::arith::dual::simplexConflicts",0),
  d_recentViolationCatches("theory::arith::dual::recentViolationCatches",0),
  d_searchTime("theory::arith::dual::searchTime")
{
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);
  StatisticsRegistry::registerStat(&d_processSignalsTime);
  StatisticsRegistry::registerStat(&d_simplexConflicts);
  StatisticsRegistry::registerStat(&d_recentViolationCatches);
  StatisticsRegistry::registerStat(&d_searchTime);
}

DualSimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);
  StatisticsRegistry::unregisterStat(&d_processSignalsTime);
  StatisticsRegistry::unregisterStat(&d_simplexConflicts);
  StatisticsRegistry::unregisterStat(&d_recentViolationCatches);
  StatisticsRegistry::unregisterStat(&d_searchTime);
}

bool SimplexDecisionProcedure::standardProcessSignals(TimerStat &timer, IntStat& conflicts) {
  TimerStat::CodeTimer codeTimer(timer);
  Assert( d_conflictVariables.empty() );


  while(d_errorSet.moreSignals()){
    ArithVar curr = d_errorSet.topSignal();
    d_errorSet.popSignal();
    if(d_tableau.isBasic(curr) && !d_variables.assignmentIsConsistent(curr)){
      d_linEq.trackVariable(curr);

      if(!d_conflictVariables.isMember(curr) &&
         checkBasicForConflict(curr)){

        Debug("recentlyViolated")
          << "It worked? "
          << conflicts.getData()
          << " " << curr
          << " "  << checkBasicForConflict(curr) << endl;
        reportConflict(curr);
        ++conflicts;
      }
    }
  }
  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
}

Result::Sat DualSimplexDecisionProcedure::dualFindModel(bool exactResult){
  Assert(d_conflictVariables.empty());

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Debug("arith::findModel") << "dualFindModel("<< instance <<") trivial" << endl;
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();

  if(processSignals()){
    d_conflictVariables.purge();

    Debug("arith::findModel") << "dualFindModel("<< instance <<") early conflict" << endl;
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Debug("arith::findModel") << "dualFindModel("<< instance <<") fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    return Result::SAT;
  }

  Debug("arith::findModel") << "dualFindModel(" << instance <<") start non-trivial" << endl;

  Result::Sat result = Result::SAT_UNKNOWN;

  static const bool verbose = false;
  exactResult |= options::arithStandardCheckVarOrderPivots() < 0;


  uint32_t checkPeriod = options::arithSimplexCheckPeriod();
  if(result == Result::SAT_UNKNOWN){
    uint32_t numDifferencePivots = options::arithHeuristicPivots() < 0 ?
      d_numVariables + 1 : options::arithHeuristicPivots();
    // The signed to unsigned conversion is safe.
    if(numDifferencePivots > 0){

      d_errorSet.setSelectionRule(d_heuristicRule);
      if(searchForFeasibleSolution(numDifferencePivots)){
        result = Result::UNSAT;
      }
    }

    if(verbose && numDifferencePivots > 0){
      if(result ==  Result::UNSAT){
        Message() << "diff order found unsat" << endl;
      }else if(d_errorSet.errorEmpty()){
        Message() << "diff order found model" << endl;
      }else{
        Message() << "diff order missed" << endl;
      }
    }
  }
  Assert(!d_errorSet.moreSignals());

  if(!d_errorSet.errorEmpty() && result != Result::UNSAT){
    if(exactResult){
      d_errorSet.setSelectionRule(VAR_ORDER);
      while(!d_errorSet.errorEmpty() && result != Result::UNSAT){
        Assert(checkPeriod > 0);
        if(searchForFeasibleSolution(checkPeriod)){
          result = Result::UNSAT;
        }
      }
    }else if( options::arithStandardCheckVarOrderPivots() > 0){
      d_errorSet.setSelectionRule(VAR_ORDER);
      if(searchForFeasibleSolution(options::arithStandardCheckVarOrderPivots())){
        result = Result::UNSAT;
      }
      if(verbose){
        if(result ==  Result::UNSAT){
          Message() << "restricted var order found unsat" << endl;
        }else if(d_errorSet.errorEmpty()){
          Message() << "restricted var order found model" << endl;
        }else{
          Message() << "restricted var order missed" << endl;
        }
      }
    }
  }

  Assert(!d_errorSet.moreSignals());
  if(result == Result::SAT_UNKNOWN && d_errorSet.errorEmpty()){
    result = Result::SAT;
  }



  d_pivotsInRound.purge();
  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Debug("arith::findModel") << "end findModel() " << instance << " " << result <<  endl;

  return result;
}

/** Reports a conflict to on the output channel. */
void SimplexDecisionProcedure::reportConflict(ArithVar basic){
  Assert(!d_conflictVariables.isMember(basic));
  Assert(checkBasicForConflict(basic));
  Node conflict = generatConflictForBasic(basic);
  Assert(!conflict.isNull());
  d_conflictChannel(conflict);
  d_conflictVariables.add(basic);
}

Node SimplexDecisionProcedure::generatConflictForBasic(ArithVar basic) const {
  
  Assert(d_tableau.isBasic(basic));
  Assert(checkBasicForConflict(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    Assert(d_linEq.nonbasicsAtUpperBounds(basic));
    return d_linEq.generateConflictBelowLowerBound(basic);
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    Assert(d_linEq.nonbasicsAtLowerBounds(basic));
    return d_linEq.generateConflictAboveUpperBound(basic);
  }else{
    Unreachable();
  }
}
Node SimplexDecisionProcedure::maybeGenerateConflictForBasic(ArithVar basic) const {
  if(checkBasicForConflict(basic)){
    return generatConflictForBasic(basic);
  }else{
    return Node::null();
  }
}

bool SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic) const {
  Assert(d_tableau.isBasic(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    if(d_linEq.nonbasicsAtUpperBounds(basic)){
      return true;
    }
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    if(d_linEq.nonbasicsAtLowerBounds(basic)){
      return true;
    }
  }
  return false;
}

//corresponds to Check() in dM06
//template <SimplexDecisionProcedure::PreferenceFunction pf>
bool DualSimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  TimerStat::CodeTimer codeTimer(d_statistics.d_searchTime);

  Debug("arith") << "searchForFeasibleSolution" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0 && !d_errorSet.focusEmpty()){
    if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }
    Assert(d_conflictVariables.empty());
    ArithVar x_i = d_errorSet.topFocusVariable();

    Debug("arith::update::select") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Debug("arith::update") << "No inconsistent variables" << endl;
      return false; //sat
    }

    --remainingIterations;

    bool useVarOrderPivot = d_pivotsInRound.count(x_i) >=  options::arithPivotThreshold();
    if(!useVarOrderPivot){
      d_pivotsInRound.add(x_i);
    }


    Debug("arith::update")
      << "pivots in rounds: " <<  d_pivotsInRound.count(x_i)
      << " use " << useVarOrderPivot
      << " threshold " << options::arithPivotThreshold()
      << endl;

    LinearEqualityModule::PreferenceFunction pf = useVarOrderPivot ?
      &LinearEqualityModule::minVarOrder : &LinearEqualityModule::minBoundAndColLength;
    
    //DeltaRational beta_i = d_variables.getAssignment(x_i);
    ArithVar x_j = ARITHVAR_SENTINEL;

    if(d_variables.cmpAssignmentLowerBound(x_i) < 0 ){
      x_j = d_linEq.selectSlackUpperBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        Unreachable();
        ++(d_statistics.d_statUpdateConflicts);
        reportConflict(x_i);
        ++(d_statistics.d_simplexConflicts);
        // Node conflict = d_linEq.generateConflictBelowLowerBound(x_i); //unsat
        // d_conflictVariable = x_i;
        // reportConflict(conflict);
        return true;
      }else{
        const DeltaRational& l_i = d_variables.getLowerBound(x_i);
        d_linEq.pivotAndUpdate(x_i, x_j, l_i);
      }
    }else if(d_variables.cmpAssignmentUpperBound(x_i) > 0){
      x_j = d_linEq.selectSlackLowerBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        Unreachable();
        ++(d_statistics.d_statUpdateConflicts);
        reportConflict(x_i);
        ++(d_statistics.d_simplexConflicts);
        // Node conflict = d_linEq.generateConflictAboveUpperBound(x_i); //unsat
        // d_conflictVariable = x_i;
        // reportConflict(conflict);
        return true;
      }else{
        const DeltaRational& u_i = d_variables.getUpperBound(x_i);
        d_linEq.pivotAndUpdate(x_i, x_j, u_i);
      }
    }
    Assert(x_j != ARITHVAR_SENTINEL);

    if(processSignals()){
      return true;
    }
  }
  Assert(!d_errorSet.focusEmpty() || d_errorSet.errorEmpty());
  Assert(remainingIterations == 0 || d_errorSet.focusEmpty());
  Assert(d_errorSet.noSignals());

  return false;
}

PureUpdateSimplexDecisionProcedure::PureUpdateSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
  , d_focusErrorVar(ARITHVAR_SENTINEL)
  , d_focusThreshold(0)
{ }

Result::Sat PureUpdateSimplexDecisionProcedure::findModel(bool exactResult){
  Assert(d_conflictVariables.empty());

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Debug("arith::findModel") << "fcFindModel("<< instance <<") trivial" << endl;
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();

  if(processSignals()){
    d_conflictVariables.purge();

    Debug("arith::findModel") << "fcFindModel("<< instance <<") early conflict" << endl;
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Debug("arith::findModel") << "fcFindModel("<< instance <<") fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    return Result::SAT;
  }

  Debug("arith::findModel") << "fcFindModel(" << instance <<") start non-trivial" << endl;

  static const bool verbose = false;
  Result::Sat result = Result::SAT_UNKNOWN;

  if(result == Result::SAT_UNKNOWN){
    if(attemptPureUpdates()){
      result = Result::UNSAT;
    }
    if(result ==  Result::UNSAT){
      ++(d_statistics.d_pureUpdateFoundUnsat);
      if(verbose){ Message() << "pure updates found unsat" << endl; }
    }else if(d_errorSet.errorEmpty()){
      ++(d_statistics.d_pureUpdateFoundSat);
      if(verbose){ Message() << "pure updates found model" << endl; }
    }else{
      ++(d_statistics.d_pureUpdateMissed);
      if(verbose){ Message() << "pure updates missed" << endl; }
    }
  }

  Assert(!d_errorSet.moreSignals());
  if(result == Result::SAT_UNKNOWN && d_errorSet.errorEmpty()){
    result = Result::SAT;
  }

  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Debug("arith::findModel") << "end findModel() " << instance << " " << result <<  endl;

  return result;
}

void PureUpdateSimplexDecisionProcedure::tearDownFocusErrorFunction(){
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  d_tableau.removeBasicRow(d_focusErrorVar);
  d_focusThreshold = DeltaRational(0);
  releaseVariable(d_focusErrorVar);

  d_focusErrorVar = ARITHVAR_SENTINEL;
  
  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
}
void PureUpdateSimplexDecisionProcedure::constructFocusErrorFunction(){
  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
  Assert(!d_errorSet.focusEmpty());
  Assert(d_focusThreshold.sgn() == 0);
  d_focusErrorVar = requestVariable();
  

  std::vector<Rational> coeffs;
  std::vector<ArithVar> variables;

  DeltaRational diff;
  for(ErrorSet::focus_iterator iter = d_errorSet.focusBegin(), end = d_errorSet.focusEnd(); iter != end; ++iter){
    ArithVar e = *iter;
    
    Assert(d_tableau.isBasic(e));
    Assert(!d_variables.assignmentIsConsistent(e));

    int sgn = d_errorSet.getSgn(e);
    coeffs.push_back(Rational(sgn));
    variables.push_back(e);

    if(sgn > 0) {
      diff = d_variables.getLowerBound(e) - d_variables.getAssignment(e);
    }else if(sgn < 0){
      diff = d_variables.getAssignment(e) - d_variables.getUpperBound(e);
    }
    Assert(diff.sgn() > 0);
    Debug("pu") << e << " " << sgn << " " << diff << endl;
    d_focusThreshold += diff;
  }
  d_tableau.addRow(d_focusErrorVar, coeffs, variables);
  DeltaRational newAssignment = d_linEq.computeRowValue(d_focusErrorVar, false);
  d_variables.setAssignment(d_focusErrorVar, newAssignment);

  Debug("pu") << d_focusErrorVar << " " << newAssignment
       << " " << d_focusThreshold << " " << endl;
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
}


PureUpdateSimplexDecisionProcedure::Statistics::Statistics():
  d_pureUpdateFoundUnsat("theory::arith::PureUpdate::FoundUnsat", 0),
  d_pureUpdateFoundSat("theory::arith::PureUpdate::FoundSat", 0),
  d_pureUpdateMissed("theory::arith::PureUpdate::Missed", 0),
  d_pureUpdates("theory::arith::PureUpdate::updates", 0),
  d_pureUpdateDropped("theory::arith::PureUpdate::dropped", 0),
  d_pureUpdateConflicts("theory::arith::PureUpdate::conflicts", 0),
  d_foundConflicts("theory::arith::PureUpdate::foundConflicts", 0),
  d_attemptPureUpdatesTimer("theory::arith::PureUpdate::timer"),
  d_processSignalsTime("theory::arith::PureUpdate::process::timer")
{
  StatisticsRegistry::registerStat(&d_pureUpdateFoundUnsat);
  StatisticsRegistry::registerStat(&d_pureUpdateFoundSat);
  StatisticsRegistry::registerStat(&d_pureUpdateMissed);
  StatisticsRegistry::registerStat(&d_pureUpdates);
  StatisticsRegistry::registerStat(&d_pureUpdateDropped);
  StatisticsRegistry::registerStat(&d_pureUpdateConflicts);

  StatisticsRegistry::registerStat(&d_foundConflicts);

  StatisticsRegistry::registerStat(&d_attemptPureUpdatesTimer);
  StatisticsRegistry::registerStat(&d_processSignalsTime);
}

PureUpdateSimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_pureUpdateFoundUnsat);
  StatisticsRegistry::unregisterStat(&d_pureUpdateFoundSat);
  StatisticsRegistry::unregisterStat(&d_pureUpdateMissed);
  StatisticsRegistry::unregisterStat(&d_pureUpdates);
  StatisticsRegistry::unregisterStat(&d_pureUpdateDropped);
  StatisticsRegistry::unregisterStat(&d_pureUpdateConflicts);

  StatisticsRegistry::unregisterStat(&d_foundConflicts);

  StatisticsRegistry::unregisterStat(&d_attemptPureUpdatesTimer);
  StatisticsRegistry::unregisterStat(&d_processSignalsTime);
}

bool PureUpdateSimplexDecisionProcedure::attemptPureUpdates(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_attemptPureUpdatesTimer);

  Assert(!d_errorSet.focusEmpty());
  Assert(d_errorSet.noSignals());

  constructFocusErrorFunction();

  LinearEqualityModule::UpdateInfo proposal;
  int boundImprovements = 0;
  int dropped = 0;
  int computations = 0;

  for( Tableau::RowIterator ri = d_tableau.basicRowIterator(d_focusErrorVar); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;

    ArithVar curr = e.getColVar();
    if(curr == d_focusErrorVar){ continue; }
    
    int dir = e.getCoefficient().sgn();
    Assert(dir != 0);

    bool worthwhile  = false;

    if( (dir > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
	(dir < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0) ){
      
      ++computations;
      d_linEq.computeSafeUpdate(curr, dir, proposal);
      if(proposal.d_errorsFixed > 0){
        worthwhile = true;
      }else if(!proposal.d_degenerate && proposal.d_limiting != NULL){
        if(proposal.d_limiting->getVariable() == curr){
          worthwhile = true;
        }
      }
      Debug("pu::refined")
        << "pure update proposal "
        << curr << " "
        << worthwhile << " "
        << proposal.d_errorsFixed << " "
        << proposal.d_degenerate<< " "
        << proposal.d_limiting << " "
        << proposal.d_value << endl;

      // worthwhile = p.first;
      // if(worthwhile && p.second == NullConstraint){
      //   uint32_t fixed = d_linEq.computeUnconstrainedUpdate(curr, dir, dr);
      //   if( fixed == 0 ){
      //     worthwhile = false;
      //   }
      //   Debug("pu") << "podsfjio!! " << fixed << endl;
      // }else if(worthwhile){
      //   Constraint c = p.second;
      //   Debug("pu::refine") << curr;
      //   if(c->getVariable() != curr){
      //     worthwhile = false;
      //     Debug("pu::refine") << " dropping ";
      //   }else{
      //     Debug("pu::refine") << " keeping ";
      //   }
      //   Debug("pu::refine") << c << endl;
      // }
    }
    if(worthwhile){
      Debug("pu") << d_variables.getAssignment(d_focusErrorVar) << endl;

      BoundCounts before = d_variables.boundCounts(curr);
      d_linEq.updateTracked(curr, proposal.d_value);
      BoundCounts after = d_variables.boundCounts(curr);

      ++d_statistics.d_pureUpdates;
      ++boundImprovements;
      Debug("pu") << boundImprovements  << ": " << curr << " before: " << before << " after: " << after << endl;
      Debug("pu") << e.getCoefficient() << endl;
      Debug("pu") << d_variables.getAssignment(d_focusErrorVar) << endl;

      uint32_t prevSize = d_errorSet.errorSize();
      Assert(d_errorSet.moreSignals());
      if(Debug.isOn("pu")){  d_errorSet.debugPrint(); }
      while(d_errorSet.moreSignals()){
        ArithVar updated = d_errorSet.topSignal();
        bool wasInError = d_errorSet.inError(updated);
        d_errorSet.popSignal();
        if(updated == curr){ continue; }
        Assert(d_tableau.isBasic(updated));        
        if(!d_linEq.basicIsTracked(updated)){continue;}


        Assert(d_linEq.basicIsTracked(updated));
        Assert(wasInError || d_variables.assignmentIsConsistent(updated));

        if(!d_variables.assignmentIsConsistent(updated)
           && checkBasicForConflict(updated)){
          Assert(!d_conflictVariables.isMember(updated) );
          Debug("pu")
            << "It worked? "
            << d_statistics.d_pureUpdateConflicts.getData()
            << " " << curr
            << " "  << checkBasicForConflict(updated) << endl;
          reportConflict(updated);
          ++(d_statistics.d_foundConflicts);
          ++(d_statistics.d_pureUpdateConflicts);
        }
      }
      if(d_conflictVariables.empty()){
        if(Debug.isOn("pu")){  d_errorSet.debugPrint(); }
        uint32_t currSize = d_errorSet.errorSize();
        Assert(currSize <= prevSize);
        if(currSize < prevSize){
          dropped+= prevSize - currSize;
          if(currSize == 0){
            break;
          }
        }
      }else{
        break;
      }
    }
  }
  tearDownFocusErrorFunction();

  (d_statistics.d_pureUpdateDropped) += dropped;

  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
