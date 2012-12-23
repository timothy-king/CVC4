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

static const bool CHECK_AFTER_PIVOT = true;

SimplexDecisionProcedure::SimplexDecisionProcedure(LinearEqualityModule& linEq, NodeCallBack& conflictChannel, ArithVarMalloc& variables) :
  d_conflictVariable(ARITHVAR_SENTINEL),
  d_linEq(linEq),
  d_variables(d_linEq.getVariables()),
  d_tableau(d_linEq.getTableau()),
  d_queue(d_variables, d_tableau),
  d_numVariables(0),
  d_conflictChannel(conflictChannel),
  d_pivotsInRound(),
  d_DELTA_ZERO(0,0),
  d_arithVarMalloc(variables)
{
  switch(ArithHeuristicPivotRule rule = options::arithHeuristicPivotRule()) {
  case MINIMUM:
    d_queue.setPivotRule(ArithPriorityQueue::MINIMUM);
    break;
  case BREAK_TIES:
    d_queue.setPivotRule(ArithPriorityQueue::BREAK_TIES);
    break;
  case MAXIMUM:
    d_queue.setPivotRule(ArithPriorityQueue::MAXIMUM);
    break;
  default:
    Unhandled(rule);
  }
}

SimplexDecisionProcedure::Statistics::Statistics():
  d_statUpdateConflicts("theory::arith::UpdateConflicts", 0),
  d_findConflictOnTheQueueTime("theory::arith::findConflictOnTheQueueTime"),
  d_attemptBeforeDiffSearch("theory::arith::qi::BeforeDiffSearch::attempt",0),
  d_successBeforeDiffSearch("theory::arith::qi::BeforeDiffSearch::success",0),
  d_attemptAfterDiffSearch("theory::arith::qi::AfterDiffSearch::attempt",0),
  d_successAfterDiffSearch("theory::arith::qi::AfterDiffSearch::success",0),
  d_attemptDuringDiffSearch("theory::arith::qi::DuringDiffSearch::attempt",0),
  d_successDuringDiffSearch("theory::arith::qi::DuringDiffSearch::success",0),
  d_attemptDuringVarOrderSearch("theory::arith::qi::DuringVarOrderSearch::attempt",0),
  d_successDuringVarOrderSearch("theory::arith::qi::DuringVarOrderSearch::success",0),
  d_attemptAfterVarOrderSearch("theory::arith::qi::AfterVarOrderSearch::attempt",0),
  d_successAfterVarOrderSearch("theory::arith::qi::AfterVarOrderSearch::success",0),
  d_simplexConflicts("theory::arith::simplexConflicts",0)
{
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);

  StatisticsRegistry::registerStat(&d_findConflictOnTheQueueTime);

  StatisticsRegistry::registerStat(&d_attemptBeforeDiffSearch);
  StatisticsRegistry::registerStat(&d_successBeforeDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptAfterDiffSearch);
  StatisticsRegistry::registerStat(&d_successAfterDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptDuringDiffSearch);
  StatisticsRegistry::registerStat(&d_successDuringDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptDuringVarOrderSearch);
  StatisticsRegistry::registerStat(&d_successDuringVarOrderSearch);
  StatisticsRegistry::registerStat(&d_attemptAfterVarOrderSearch);
  StatisticsRegistry::registerStat(&d_successAfterVarOrderSearch);

  StatisticsRegistry::registerStat(&d_simplexConflicts);
}

SimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);

  StatisticsRegistry::unregisterStat(&d_findConflictOnTheQueueTime);

  StatisticsRegistry::unregisterStat(&d_attemptBeforeDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successBeforeDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptAfterDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successAfterDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptDuringDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successDuringDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptDuringVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_successDuringVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_attemptAfterVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_successAfterVarOrderSearch);

  StatisticsRegistry::unregisterStat(&d_simplexConflicts);
}

bool SimplexDecisionProcedure::findConflictOnTheQueue(SearchPeriod type) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_findConflictOnTheQueueTime);
  Assert(d_successes.empty());

  switch(type){
  case BeforeDiffSearch:     ++(d_statistics.d_attemptBeforeDiffSearch); break;
  case DuringDiffSearch:     ++(d_statistics.d_attemptDuringDiffSearch); break;
  case AfterDiffSearch:      ++(d_statistics.d_attemptAfterDiffSearch); break;
  case DuringVarOrderSearch: ++(d_statistics.d_attemptDuringVarOrderSearch); break;
  case AfterVarOrderSearch:  ++(d_statistics.d_attemptAfterVarOrderSearch); break;
  }

  ArithPriorityQueue::const_iterator i = d_queue.begin();
  ArithPriorityQueue::const_iterator end = d_queue.end();
  for(; i != end; ++i){
    ArithVar x_i = *i;

    if(x_i != d_conflictVariable && d_tableau.isBasic(x_i) && !d_successes.isMember(x_i)){
      Node possibleConflict = checkBasicForConflict(x_i);
      if(!possibleConflict.isNull()){
        d_successes.add(x_i);
        reportConflict(possibleConflict);
      }
    }
  }
  if(!d_successes.empty()){
    switch(type){
    case BeforeDiffSearch:     ++(d_statistics.d_successBeforeDiffSearch); break;
    case DuringDiffSearch:     ++(d_statistics.d_successDuringDiffSearch); break;
    case AfterDiffSearch:      ++(d_statistics.d_successAfterDiffSearch); break;
    case DuringVarOrderSearch: ++(d_statistics.d_successDuringVarOrderSearch); break;
    case AfterVarOrderSearch:  ++(d_statistics.d_successAfterVarOrderSearch); break;
    }
    d_successes.purge();
    return true;
  }else{
    return false;
  }
}

Result::Sat SimplexDecisionProcedure::dualFindModel(bool exactResult){
  Assert(d_conflictVariable == ARITHVAR_SENTINEL);
  Assert(d_queue.inCollectionMode());

  if(d_queue.empty()){
    return Result::SAT;
  }
  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;
  Debug("arith::findModel") << "begin findModel()" << instance << endl;

  d_queue.transitionToDifferenceMode();

  Result::Sat result = Result::SAT_UNKNOWN;

  if(d_queue.empty()){
    result = Result::SAT;
  }else if(d_queue.size() > 1){
    if(findConflictOnTheQueue(BeforeDiffSearch)){
      result = Result::UNSAT;
    }
  }

  static const bool verbose = false;
  exactResult |= options::arithStandardCheckVarOrderPivots() < 0;
  const uint32_t inexactResultsVarOrderPivots = exactResult ? 0 : options::arithStandardCheckVarOrderPivots();

  uint32_t checkPeriod = options::arithSimplexCheckPeriod();
  if(result == Result::SAT_UNKNOWN){
    uint32_t numDifferencePivots = options::arithHeuristicPivots() < 0 ?
      d_numVariables + 1 : options::arithHeuristicPivots();
    // The signed to unsigned conversion is safe.
    uint32_t pivotsRemaining = numDifferencePivots;
    while(!d_queue.empty() &&
          result != Result::UNSAT &&
          pivotsRemaining > 0){
      uint32_t pivotsToDo = min(checkPeriod, pivotsRemaining);
      pivotsRemaining -= pivotsToDo;
      if(searchForFeasibleSolution(pivotsToDo)){
        result = Result::UNSAT;
      }//Once every CHECK_PERIOD examine the entire queue for conflicts
      if(result != Result::UNSAT){
        if(findConflictOnTheQueue(DuringDiffSearch)) { result = Result::UNSAT; }
      }else{
        findConflictOnTheQueue(AfterDiffSearch); // already unsat
      }
    }

    if(verbose && numDifferencePivots > 0){
      if(result ==  Result::UNSAT){
        Message() << "diff order found unsat" << endl;
      }else if(d_queue.empty()){
        Message() << "diff order found model" << endl;
      }else{
        Message() << "diff order missed" << endl;
      }
    }
  }

  if(!d_queue.empty() && result != Result::UNSAT){
    if(exactResult){
      d_queue.transitionToVariableOrderMode();

      while(!d_queue.empty() && result != Result::UNSAT){
        if(searchForFeasibleSolution(checkPeriod)){
          result = Result::UNSAT;
        }

        //Once every CHECK_PERIOD examine the entire queue for conflicts
        if(result != Result::UNSAT){
          if(findConflictOnTheQueue(DuringVarOrderSearch)){
            result = Result::UNSAT;
          }
        } else{
          findConflictOnTheQueue(AfterVarOrderSearch);
        }
      }
      if(verbose){
        if(result ==  Result::UNSAT){
          Message() << "bland found unsat" << endl;
        }else if(d_queue.empty()){
          Message() << "bland found model" << endl;
        }else{
          Message() << "bland order missed" << endl;
        }
      }
    }else{
      d_queue.transitionToVariableOrderMode();

      if(searchForFeasibleSolution(inexactResultsVarOrderPivots)){
        result = Result::UNSAT;
        findConflictOnTheQueue(AfterVarOrderSearch); // already unsat
      }else{
        if(findConflictOnTheQueue(AfterVarOrderSearch)) { result = Result::UNSAT; }
      }

      if(verbose){
        if(result ==  Result::UNSAT){
          Message() << "restricted var order found unsat" << endl;
        }else if(d_queue.empty()){
          Message() << "restricted var order found model" << endl;
        }else{
          Message() << "restricted var order missed" << endl;
        }
      }
    }
  }

  if(result == Result::SAT_UNKNOWN && d_queue.empty()){
    result = Result::SAT;
  }



  d_pivotsInRound.purge();
  // ensure that the conflict variable is still in the queue.
  if(d_conflictVariable != ARITHVAR_SENTINEL){
    d_queue.enqueueIfInconsistent(d_conflictVariable);
  }
  d_conflictVariable = ARITHVAR_SENTINEL;

  d_queue.transitionToCollectionMode();
  Assert(d_queue.inCollectionMode());
  Debug("arith::findModel") << "end findModel() " << instance << " " << result <<  endl;
  return result;
}

Node SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic){

  Assert(d_tableau.isBasic(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    // ArithVar x_j = d_linEq.anySlackUpperBound(basic);
    // if(x_j == ARITHVAR_SENTINEL ){
    //   return d_linEq.generateConflictBelowLowerBound(basic);
    // }
    if(d_linEq.nonbasicsAtLowerBounds(basic)){
      return d_linEq.generateConflictBelowLowerBound(basic);
    }
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    // ArithVar x_j = d_linEq.anySlackLowerBound(basic);
    // if(x_j == ARITHVAR_SENTINEL ){
    //   return d_linEq.generateConflictAboveUpperBound(basic);
    // }
    if(d_linEq.nonbasicsAtUpperBounds(basic)){
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

    ArithVar x_i = d_queue.dequeueInconsistentBasicVariable();
    Debug("arith::update::select") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Debug("arith_update") << "No inconsistent variables" << endl;
      return false; //sat
    }

    --remainingIterations;

    bool useVarOrderPivot = d_pivotsInRound.count(x_i) >=  options::arithPivotThreshold();
    if(!useVarOrderPivot){
      d_pivotsInRound.add(x_i);
    }


    Debug("playground") << "pivots in rounds: " <<  d_pivotsInRound.count(x_i)
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
        ++(d_statistics.d_statUpdateConflicts);
        Node conflict = d_linEq.generateConflictBelowLowerBound(x_i); //unsat
        d_conflictVariable = x_i;
        reportConflict(conflict);
        return true;
      }
      const DeltaRational& l_i = d_variables.getLowerBound(x_i);
      d_linEq.pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_variables.cmpAssignmentUpperBound(x_i) > 0){
      x_j = d_linEq.selectSlackLowerBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        Node conflict = d_linEq.generateConflictAboveUpperBound(x_i); //unsat

        d_conflictVariable = x_i;
        reportConflict(conflict);
        return true;
      }
      const DeltaRational& u_i = d_variables.getUpperBound(x_i);
      d_linEq.pivotAndUpdate(x_i, x_j, u_i);
    }
    Assert(x_j != ARITHVAR_SENTINEL);

    //Check to see if we already have a conflict with x_j to prevent wasteful work
    if(CHECK_AFTER_PIVOT){
      Node possibleConflict = checkBasicForConflict(x_j);
      if(!possibleConflict.isNull()){
        d_conflictVariable = x_j;
        reportConflict(possibleConflict);
        return true; // unsat
      }
    }
  }
  Assert(remainingIterations == 0);

  return false;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
