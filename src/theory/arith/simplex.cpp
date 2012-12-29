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

SimplexDecisionProcedure::SimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : d_conflictVariables()
  , d_linEq(linEq)
  , d_variables(d_linEq.getVariables())
  , d_tableau(d_linEq.getTableau())
  , d_errorSet(errors)
  , d_numVariables(0)
  , d_conflictChannel(conflictChannel)
  , d_pivotsInRound()
  , d_arithVarMalloc(tvmalloc)
{
  d_heuristicRule = options::arithErrorSelectionRule();
  d_errorSet.setSelectionRule(d_heuristicRule);
}

SimplexDecisionProcedure::Statistics::Statistics():
  d_statUpdateConflicts("theory::arith::UpdateConflicts", 0),
  d_processSignalsTime("theory::arith::findConflictOnTheQueueTime"),
  d_simplexConflicts("theory::arith::simplexConflicts",0),
  d_recentViolationCatches("theory::arith::recentViolationCatches",0),
  d_searchTime("theory::arith::searchTime")
{
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);
  StatisticsRegistry::registerStat(&d_processSignalsTime);
  StatisticsRegistry::registerStat(&d_simplexConflicts);
  StatisticsRegistry::registerStat(&d_recentViolationCatches);
  StatisticsRegistry::registerStat(&d_searchTime);
}

SimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);
  StatisticsRegistry::unregisterStat(&d_processSignalsTime);
  StatisticsRegistry::unregisterStat(&d_simplexConflicts);
  StatisticsRegistry::unregisterStat(&d_recentViolationCatches);
  StatisticsRegistry::unregisterStat(&d_searchTime);
}

bool SimplexDecisionProcedure::processSignals() {
  TimerStat::CodeTimer codeTimer(d_statistics.d_processSignalsTime);
  Assert( d_conflictVariables.empty() );


  while(d_errorSet.moreSignals()){
    ArithVar curr = d_errorSet.topSignal();
    d_errorSet.popSignal();
    if(d_tableau.isBasic(curr)){
      d_linEq.maybeTrackVariable(curr);

      if(!d_variables.assignmentIsConsistent(curr) &&
         !d_conflictVariables.isMember(curr) &&
         checkBasicForConflict(curr)){

        Debug("recentlyViolated")
          << "It worked? "
          << d_statistics.d_recentViolationCatches.getData()
          << " " << curr
          << " "  << checkBasicForConflict(curr) << endl;
        reportConflict(curr);
        ++(d_statistics.d_recentViolationCatches);
      }
    }
  }
  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
}

Result::Sat SimplexDecisionProcedure::dualFindModel(bool exactResult){
  Assert(d_conflictVariables.empty());

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;

  // We need to reduce this because of
  d_errorSet.reduce();

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Debug("arith::findModel") << "dualFindModel("<< instance <<") trivial" << endl;
    return Result::SAT;
  }

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

  static const bool verbose = true;
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
  ++(d_statistics.d_simplexConflicts);
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
bool SimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  TimerStat::CodeTimer codeTimer(d_statistics.d_searchTime);

  Debug("arith") << "searchForFeasibleSolution" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0 && !d_errorSet.focusEmpty()){
    if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

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

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
