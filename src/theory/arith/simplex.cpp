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
  d_recentViolationCatches("theory::arith::recentViolationCatches",0)
{
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);
  StatisticsRegistry::registerStat(&d_processSignalsTime);
  StatisticsRegistry::registerStat(&d_simplexConflicts);
  StatisticsRegistry::registerStat(&d_recentViolationCatches);
}

SimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);
  StatisticsRegistry::unregisterStat(&d_processSignalsTime);
  StatisticsRegistry::unregisterStat(&d_simplexConflicts);
  StatisticsRegistry::unregisterStat(&d_recentViolationCatches);
}

bool SimplexDecisionProcedure::processSignals() {
  TimerStat::CodeTimer codeTimer(d_statistics.d_processSignalsTime);
  Assert( d_conflictVariables.empty() );


  while(!d_errorSet.moreSignals()){
    ArithVar curr = d_errorSet.topSignal();
    d_errorSet.popSignal();
    d_linEq.maybeTrackVariable(curr);

    if(d_tableau.isBasic(curr) &&
       !d_variables.assignmentIsConsistent(curr) &&
       !d_conflictVariables.isMember(curr)){

      Debug("recentlyViolated")
        << "It worked? "
        << d_statistics.d_recentViolationCatches.getData()
        << " " << curr
        << " "  << checkBasicForConflict(curr) << endl;
      reportConflict(curr);
      ++(d_statistics.d_recentViolationCatches);
    }
  }
  return !d_conflictVariables.empty();
}

Result::Sat SimplexDecisionProcedure::dualFindModel(bool exactResult){
  Assert(d_conflictVariables.empty());

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;

  if(d_errorSet.empty() && !d_errorSet.moreSignals()){
    Debug("arith::findModel") << "dualFindModel("<< instance <<") trivial" << endl;
    return Result::SAT;
  }

  d_errorSet.setSelectionRule(d_heuristicRule);

  if(processSignals()){
    d_conflictVariables.purge();

    Debug("arith::findModel") << "dualFindModel("<< instance <<") early conflict" << endl;
    return Result::UNSAT;
  }else if(d_errorSet.empty()){
    Debug("arith::findModel") << "dualFindModel("<< instance <<") fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    return Result::SAT;
  }

  Debug("arith::findModel") << "dualFindModel(" << instance <<") start non-trivial" << endl;

  Result::Sat result = Result::SAT_UNKNOWN;

  static const bool verbose = false;
  exactResult |= options::arithStandardCheckVarOrderPivots() < 0;
  const uint32_t inexactResultsVarOrderPivots = exactResult ? 0 : options::arithStandardCheckVarOrderPivots();

  uint32_t checkPeriod = options::arithSimplexCheckPeriod();
  if(result == Result::SAT_UNKNOWN){
    uint32_t numDifferencePivots = options::arithHeuristicPivots() < 0 ?
      d_numVariables + 1 : options::arithHeuristicPivots();
    // The signed to unsigned conversion is safe.
    
    if(searchForFeasibleSolution(numDifferencePivots)){
      result = Result::UNSAT;
    }

    // while(!d_errorSet.empty() &&
    //       result != Result::UNSAT &&
    //       pivotsRemaining > 0){
    //   uint32_t pivotsToDo = min(checkPeriod, pivotsRemaining);
    //   pivotsRemaining -= pivotsToDo;
    //   if(searchForFeasibleSolution(pivotsToDo)){
    //     result = Result::UNSAT;
    //   }//Once every CHECK_PERIOD examine the entire queue for conflicts
    //   if(result != Result::UNSAT){
    //     if(findConflictOnTheQueue(DuringDiffSearch)) { result = Result::UNSAT; }
    //   }else{
    //     findConflictOnTheQueue(AfterDiffSearch); // already unsat
    //   }
    // }

    if(verbose && numDifferencePivots > 0){
      if(result ==  Result::UNSAT){
        Message() << "diff order found unsat" << endl;
      }else if(d_errorSet.empty()){
        Message() << "diff order found model" << endl;
      }else{
        Message() << "diff order missed" << endl;
      }
    }
  }
  Assert(d_errorSet.moreSignals());

  if(!d_errorSet.empty() && result != Result::UNSAT){
    if(exactResult){
      d_errorSet.setSelectionRule(VAR_ORDER);
      while(!d_errorSet.empty() && result != Result::UNSAT){
        if(searchForFeasibleSolution(checkPeriod)){
          result = Result::UNSAT;
        }
      }
    }else{
      if(searchForFeasibleSolution(inexactResultsVarOrderPivots)){
        result = Result::UNSAT;
      }
    }
  }

  //     d_queue.transitionToVariableOrderMode();

  //     while(!d_queue.empty() && result != Result::UNSAT){
  //       if(searchForFeasibleSolution(checkPeriod)){
  //         result = Result::UNSAT;
  //       }

  //       //Once every CHECK_PERIOD examine the entire queue for conflicts
  //       if(result != Result::UNSAT){
  //         if(findConflictOnTheQueue(DuringVarOrderSearch)){
  //           result = Result::UNSAT;
  //         }
  //       } else{
  //         findConflictOnTheQueue(AfterVarOrderSearch);
  //       }
  //     }
  //     if(verbose){
  //       if(result ==  Result::UNSAT){
  //         Message() << "bland found unsat" << endl;
  //       }else if(d_queue.empty()){
  //         Message() << "bland found model" << endl;
  //       }else{
  //         Message() << "bland order missed" << endl;
  //       }
  //     }
  //   }else{
  //     d_queue.transitionToVariableOrderMode();

  //     if(searchForFeasibleSolution(inexactResultsVarOrderPivots)){
  //       result = Result::UNSAT;
  //       findConflictOnTheQueue(AfterVarOrderSearch); // already unsat
  //     }else{
  //       if(findConflictOnTheQueue(AfterVarOrderSearch)) { result = Result::UNSAT; }
  //     }

  //     if(verbose){
  //       if(result ==  Result::UNSAT){
  //         Message() << "restricted var order found unsat" << endl;
  //       }else if(d_queue.empty()){
  //         Message() << "restricted var order found model" << endl;
  //       }else{
  //         Message() << "restricted var order missed" << endl;
  //       }
  //     }
  //   }
  // }

  Assert(!d_errorSet.moreSignals());
  if(result == Result::SAT_UNKNOWN && d_errorSet.empty()){
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
  Node conflict = checkBasicForConflict(basic);
  Assert(!conflict.isNull());
  d_conflictChannel(conflict);
  d_conflictVariables.add(basic);
  ++(d_statistics.d_simplexConflicts);
}

Node SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic) const {

  Assert(d_tableau.isBasic(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    // ArithVar x_j = d_linEq.anySlackUpperBound(basic);
    // if(x_j == ARITHVAR_SENTINEL ){
    //   return d_linEq.generateConflictBelowLowerBound(basic);
    // }
    if(d_linEq.nonbasicsAtUpperBounds(basic)){
      return d_linEq.generateConflictBelowLowerBound(basic);
    }
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    // ArithVar x_j = d_linEq.anySlackLowerBound(basic);
    // if(x_j == ARITHVAR_SENTINEL ){
    //   return d_linEq.generateConflictAboveUpperBound(basic);
    // }
    if(d_linEq.nonbasicsAtLowerBounds(basic)){
      return d_linEq.generateConflictAboveUpperBound(basic);
    }
  }
  return Node::null();
}

//corresponds to Check() in dM06
//template <SimplexDecisionProcedure::PreferenceFunction pf>
bool SimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  Debug("arith") << "searchForFeasibleSolution" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0){
    if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

    ArithVar x_i = d_errorSet.topFocusVariable();

    //ArithVar x_i = d_queue.dequeueInconsistentBasicVariable();
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
    // //Check to see if we already have a conflict with x_j to prevent wasteful work
    // while(!d_recentlyViolated.empty()){
    //   ArithVar back = d_recentlyViolated.back();
    //   d_recentlyViolated.pop_back();

    //   Node possibleConflict = checkBasicForConflict(back);
    //   if(!possibleConflict.isNull()){
    //     ++(d_statistics.d_recentViolationCatches);
    //     Debug("recentlyViolated") << "It worked? " << d_statistics.d_recentViolationCatches.getData()
    //                               << " " << back << " "  << possibleConflict << endl;
    //     d_conflictVariable = back;
    //     reportConflict(possibleConflict);
    //     return true; // unsat
    //   }
    // }
  }
  Assert(remainingIterations == 0);

  return false;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
