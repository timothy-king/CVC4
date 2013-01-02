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
#include "theory/arith/constraint.h"

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
  , d_arithVarMalloc(tvmalloc)
  , d_errorSize(0)
  , d_focusSize(0)
  , d_focusErrorVar(ARITHVAR_SENTINEL)
  , d_focusSgns()
{
  d_heuristicRule = options::arithErrorSelectionRule();
  d_errorSet.setSelectionRule(d_heuristicRule);
}

bool SimplexDecisionProcedure::standardProcessSignals(TimerStat &timer, IntStat& conflicts) {
  TimerStat::CodeTimer codeTimer(timer);
  Assert( d_conflictVariables.empty() );


  while(d_errorSet.moreSignals()){
    ArithVar curr = d_errorSet.topSignal();
    if(d_tableau.isBasic(curr) && !d_variables.assignmentIsConsistent(curr)){
      d_linEq.trackVariable(curr);

      if(!d_conflictVariables.isMember(curr) && checkBasicForConflict(curr)){

        Debug("recentlyViolated")
          << "It worked? "
          << conflicts.getData()
          << " " << curr
          << " "  << checkBasicForConflict(curr) << endl;
        reportConflict(curr);
        ++conflicts;
      }
    }
    // Pop signal afterwards in case d_linEq.trackVariable(curr);
    // is needed for for the ErrorSet
    d_errorSet.popSignal();
  }

  d_errorSize = d_errorSet.errorSize();
  d_focusSize = d_errorSet.focusSize();

  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
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
  Assert(d_linEq.basicIsTracked(basic));

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

void SimplexDecisionProcedure::tearDownFocusErrorFunction(){
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  d_tableau.removeBasicRow(d_focusErrorVar);
  releaseVariable(d_focusErrorVar);

  d_focusErrorVar = ARITHVAR_SENTINEL;
  
  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
}
void SimplexDecisionProcedure::constructFocusErrorFunction(){
  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
  Assert(!d_errorSet.focusEmpty());
  d_focusErrorVar = requestVariable();
  

  std::vector<Rational> coeffs;
  std::vector<ArithVar> variables;

  for(ErrorSet::focus_iterator iter = d_errorSet.focusBegin(), end = d_errorSet.focusEnd(); iter != end; ++iter){
    ArithVar e = *iter;
    
    Assert(d_tableau.isBasic(e));
    Assert(!d_variables.assignmentIsConsistent(e));

    int sgn = d_errorSet.getSgn(e);
    coeffs.push_back(Rational(sgn));
    variables.push_back(e);
  }
  d_tableau.addRow(d_focusErrorVar, coeffs, variables);
  DeltaRational newAssignment = d_linEq.computeRowValue(d_focusErrorVar, false);
  d_variables.setAssignment(d_focusErrorVar, newAssignment);

  Debug("pu") << d_focusErrorVar << " " << newAssignment << endl;
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
}


// PureUpdateSimplexDecisionProcedure::Statistics::Statistics():
//   d_pureUpdateFoundUnsat("theory::arith::PureUpdate::FoundUnsat", 0),
//   d_pureUpdateFoundSat("theory::arith::PureUpdate::FoundSat", 0),
//   d_pureUpdateMissed("theory::arith::PureUpdate::Missed", 0),
//   d_pureUpdates("theory::arith::PureUpdate::updates", 0),
//   d_pureUpdateDropped("theory::arith::PureUpdate::dropped", 0),
//   d_pureUpdateConflicts("theory::arith::PureUpdate::conflicts", 0),
//   d_foundConflicts("theory::arith::PureUpdate::foundConflicts", 0),
//   d_attemptPureUpdatesTimer("theory::arith::PureUpdate::timer"),
//   d_processSignalsTime("theory::arith::PureUpdate::process::timer")
// {
//   StatisticsRegistry::registerStat(&d_pureUpdateFoundUnsat);
//   StatisticsRegistry::registerStat(&d_pureUpdateFoundSat);
//   StatisticsRegistry::registerStat(&d_pureUpdateMissed);
//   StatisticsRegistry::registerStat(&d_pureUpdates);
//   StatisticsRegistry::registerStat(&d_pureUpdateDropped);
//   StatisticsRegistry::registerStat(&d_pureUpdateConflicts);

//   StatisticsRegistry::registerStat(&d_foundConflicts);

//   StatisticsRegistry::registerStat(&d_attemptPureUpdatesTimer);
//   StatisticsRegistry::registerStat(&d_processSignalsTime);
// }

// PureUpdateSimplexDecisionProcedure::Statistics::~Statistics(){
//   StatisticsRegistry::unregisterStat(&d_pureUpdateFoundUnsat);
//   StatisticsRegistry::unregisterStat(&d_pureUpdateFoundSat);
//   StatisticsRegistry::unregisterStat(&d_pureUpdateMissed);
//   StatisticsRegistry::unregisterStat(&d_pureUpdates);
//   StatisticsRegistry::unregisterStat(&d_pureUpdateDropped);
//   StatisticsRegistry::unregisterStat(&d_pureUpdateConflicts);

//   StatisticsRegistry::unregisterStat(&d_foundConflicts);

//   StatisticsRegistry::unregisterStat(&d_attemptPureUpdatesTimer);
//   StatisticsRegistry::unregisterStat(&d_processSignalsTime);
// }

// bool PureUpdateSimplexDecisionProcedure::attemptPureUpdates(){
//   TimerStat::CodeTimer codeTimer(d_statistics.d_attemptPureUpdatesTimer);

//   Assert(!d_errorSet.focusEmpty());
//   Assert(d_errorSet.noSignals());

//   constructFocusErrorFunction();

//   UpdateInfo proposal;
//   int boundImprovements = 0;
//   int dropped = 0;
//   int computations = 0;

//   for( Tableau::RowIterator ri = d_tableau.basicRowIterator(d_focusErrorVar); !ri.atEnd(); ++ri){
//     const Tableau::Entry& e = *ri;

//     ArithVar curr = e.getColVar();
//     if(curr == d_focusErrorVar){ continue; }
    
//     int dir = e.getCoefficient().sgn();
//     Assert(dir != 0);

//     bool worthwhile  = false;

//     if( (dir > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
// 	(dir < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0) ){
      
//       ++computations;
//       proposal.d_nonbasic = curr;
//       proposal.d_sgn = dir;
//       d_linEq.computeSafeUpdate(proposal, &LinearEqualityModule::noPreference);

//       worthwhile = proposal.d_errorsFixed > 0 ||
//         (!proposal.d_degenerate &&
//          d_variables.boundCounts(curr).isZero() &&
//          proposal.d_limiting != NULL &&
//          proposal.d_limiting->getVariable() == curr);

//       Debug("pu::refined")
//         << "pure update proposal "
//         << curr << " "
//         << worthwhile << " "
//         << proposal.d_errorsFixed << " "
//         << proposal.d_degenerate<< " "
//         << proposal.d_limiting << " "
//         << proposal.d_value << endl;

//       // worthwhile = p.first;
//       // if(worthwhile && p.second == NullConstraint){
//       //   uint32_t fixed = d_linEq.computeUnconstrainedUpdate(curr, dir, dr);
//       //   if( fixed == 0 ){
//       //     worthwhile = false;
//       //   }
//       //   Debug("pu") << "podsfjio!! " << fixed << endl;
//       // }else if(worthwhile){
//       //   Constraint c = p.second;
//       //   Debug("pu::refine") << curr;
//       //   if(c->getVariable() != curr){
//       //     worthwhile = false;
//       //     Debug("pu::refine") << " dropping ";
//       //   }else{
//       //     Debug("pu::refine") << " keeping ";
//       //   }
//       //   Debug("pu::refine") << c << endl;
//       // }
//     }
//     if(worthwhile){
//       Debug("pu") << d_variables.getAssignment(d_focusErrorVar) << endl;

//       BoundCounts before = d_variables.boundCounts(curr);
//       d_linEq.updateTracked(curr, proposal.d_value);
//       BoundCounts after = d_variables.boundCounts(curr);

//       ++d_statistics.d_pureUpdates;
//       ++boundImprovements;
//       Debug("pu") << boundImprovements  << ": " << curr << " before: " << before << " after: " << after << endl;
//       Debug("pu") << e.getCoefficient() << endl;
//       Debug("pu") << d_variables.getAssignment(d_focusErrorVar) << endl;

//       uint32_t prevSize = d_errorSet.errorSize();
//       Assert(d_errorSet.moreSignals());
//       if(Debug.isOn("pu")){  d_errorSet.debugPrint(); }
//       while(d_errorSet.moreSignals()){
//         ArithVar updated = d_errorSet.topSignal();
//         bool wasInError = d_errorSet.inError(updated);
//         d_errorSet.popSignal();
//         if(updated == curr){ continue; }
//         Assert(d_tableau.isBasic(updated));        
//         if(!d_linEq.basicIsTracked(updated)){continue;}


//         Assert(d_linEq.basicIsTracked(updated));
//         Assert(wasInError || d_variables.assignmentIsConsistent(updated));

//         if(!d_variables.assignmentIsConsistent(updated)
//            && checkBasicForConflict(updated)){
//           Assert(!d_conflictVariables.isMember(updated) );
//           Debug("pu")
//             << "It worked? "
//             << d_statistics.d_pureUpdateConflicts.getData()
//             << " " << curr
//             << " "  << checkBasicForConflict(updated) << endl;
//           reportConflict(updated);
//           ++(d_statistics.d_foundConflicts);
//           ++(d_statistics.d_pureUpdateConflicts);
//         }
//       }
//       if(d_conflictVariables.empty()){
//         if(Debug.isOn("pu")){  d_errorSet.debugPrint(); }
//         uint32_t currSize = d_errorSet.errorSize();
//         Assert(currSize <= prevSize);
//         if(currSize < prevSize){
//           dropped+= prevSize - currSize;
//           if(currSize == 0){
//             break;
//           }
//         }
//       }else{
//         break;
//       }
//     }
//   }
//   tearDownFocusErrorFunction();

//   (d_statistics.d_pureUpdateDropped) += dropped;

//   Assert(d_errorSet.noSignals());
//   return !d_conflictVariables.empty();
// }

// void FCSimplexDecisionProcedure::reajustSizesAfterSignals(){
//   uint32_t newErrorSize = d_errorSet.errorSize();
//   uint32_t newFocusSize = d_errorSet.focusSize();

//   Assert(newFocusSize <= d_focusSize);
//   Assert(newErrorSize <= d_errorSize);
//   if( newFocusSize == 0 ){
//     tearDownFocusErrorFunction();
//   }else if(newFocusSize < d_focusSize){
//     reconstructFocusErrorFunction();
//   }
//   d_errorSize = newErrorSize;
//   d_focusSize = newFocusSize;
// }

// FCSimplexDecisionProcedure::FCSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
//   : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
//   , d_pivotBudget(-1)
//   , d_prevPivotImprovement(ErrorDropped)
//   , d_pivotImprovementInARow(0)
//   , d_sgnDisagreement()
//   , d_statistics()
// { }

void SimplexDecisionProcedure::loadFocusSigns(){
  Assert(d_focusSgns.empty());
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(d_focusErrorVar); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    d_focusSgns.set(curr, e.getCoefficient().sgn());
  }
}

void SimplexDecisionProcedure::unloadFocusSigns(){
  d_focusSgns.purge();
}

int SimplexDecisionProcedure::focusSgn(ArithVar nb) const {
  if(d_focusSgns.isKey(nb)){
    return d_focusSgns[nb];
  }else{
    return 0;
  }
}

// UpdateInfo FCSimplexDecisionProcedure::selectPrimalUpdate(ArithVar basic, int sgn, LinearEqualityModule::UpdatePreferenceFunction upf, LinearEqualityModule::VarPreferenceFunction bpf, bool storeDisagreements) {
//   UpdateInfo currProposal;
//   UpdateInfo selected;

//   if(storeDisagreements){
//     loadFocusSigns();
//   }
  
//   selected.d_nonbasic = ARITHVAR_SENTINEL;
//   for(Tableau::RowIterator ri = d_tableau.basicRowIterator(basic); !ri.atEnd(); ++ri){
//     const Tableau::Entry& e = *ri;
//     ArithVar curr = e.getColVar();
//     if(curr == basic){ continue; }

//     int curr_movement = sgn * e.getCoefficient().sgn();
//     bool candidate = 
//       (curr_movement > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
//       (curr_movement < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0);
//     if(!candidate) { continue; }

//     if(storeDisagreements && curr_movement != focusSgn(curr)){
//       d_sgnDisagreement.push_back(curr);
//       continue;
//     }
    
//     currProposal.d_nonbasic = curr;
//     currProposal.d_sgn = curr_movement;
//     d_linEq.computeSafeUpdate(currProposal, bpf);
    
//     if(selected.d_nonbasic == ARITHVAR_SENTINEL ||
//        (d_linEq.*upf)(selected, currProposal)){
//       selected = currProposal;
//       if(selected.d_errorsFixed > 0){
//         break;
//       }
//     }
//   }

//   if(storeDisagreements){
//     unloadFocusSigns();
//   }
  
//   return selected;
// }

// uint32_t FCSimplexDecisionProcedure::primalImproveError(ArithVar errorVar){
//   int sgn = d_errorSet.getSgn(errorVar);

//   while(d_pivotBudget != 0 && !d_conflictVariables.empty()){
//     bool useBlands = degeneratePivotsInARow() >= s_maxDegeneratePivotsBeforeBlands;
//     UpdateInfo selected = selectUpdateForPrimal (errorVar, sgn, useBlands);
//     updateAndSignal(selected);
//     logPivot(selected, useBlands);

//     if(selected.d_errorsFixed > 0){
//       // implicit subcase is if evar is no longer in error
//       return selected.d_errorsFixed > 0;
//     }
//   }
//   return 0;
// }


// void FCSimplexDecisionProcedure::focusUsingSignDisagreements(ArithVar basic, int dir){
//   Assert(!d_sgnDisagreement.empty());
//   uint32_t focusSize = d_errorSet.focusSize();
//   ArithVar nb = d_linEq.minBy(d_sgnDisagreement, &LinearEqualityModule::minColLength);
//   const Tableau::Entry& e_evar_nb = d_tableau.basicFindEntry(basic, nb);
//   int movement = dir * (e_evar_nb.getCoefficient().sgn());
//   int opposite = -movement;

//   Tableau::ColIterator colIter = d_tableau.colIterator(nb);
//   for(; !colIter.atEnd(); ++colIter){
//     const Tableau::Entry& entry = *colIter;
//     Assert(entry.getColVar() == nb);

//     if(entry.getCoefficient().sgn() == opposite){
//       ArithVar basic = d_tableau.rowIndexToBasic(entry.getRowIndex());
//       if(d_errorSet.inFocus(basic)){
//         d_errorSet.dropFromFocus(basic);
//         Debug("arith::dropp") << "dropping from focus " << basic << endl; 
//       }
//     }
//   }
//   d_sgnDisagreement.clear();
//   Assert(focusSize > d_errorSet.focusSize());
//   Assert(d_errorSet.focusSize() >= 1);

//   reconstructFocusErrorFunction();

// }

// void FCSimplexDecisionProcedure::updateAndSignal(const UpdateInfo& selected){
//   ArithVar nonbasic = selected.d_nonbasic;
//   Constraint limiting = selected.d_limiting;
//   if(limiting == NULL){
//     // This must drop at least the current variable
//     Assert(selected.d_errorsFixed > 0);
//     d_linEq.updateTracked(nonbasic, selected.d_value);
//   }else if(nonbasic == limiting->getVariable()){
//     d_linEq.updateTracked(nonbasic, selected.d_value);
//   }else{
//     ArithVar basic = limiting->getVariable();
//     d_linEq.trackVariable(basic);
//     d_linEq.pivotAndUpdate(basic, nonbasic, limiting->getValue());
//   }

//   while(d_errorSet.moreSignals()){
//     ArithVar updated = d_errorSet.topSignal();
//     d_errorSet.popSignal();

//     if(d_tableau.isBasic(updated) &&
//        !d_variables.assignmentIsConsistent(updated) &&
//        checkBasicForConflict(updated)){
//       reportConflict(updated);
//     }
//   }
//   reajustSizesAfterSignals();
// }

// uint32_t FCSimplexDecisionProcedure::dualLikeImproveError(ArithVar errorVar){
//   uint32_t dropped = 0;

//   int sgn = d_errorSet.getSgn(errorVar);
//   UpdateInfo selected = selectUpdateForDualLike(errorVar, sgn);

//   if(selected.d_nonbasic == ARITHVAR_SENTINEL){
//     // we found no proposals
//     // If this is empty, there must be an error on this variable!
//     // this should not be possible
//     Assert(!d_sgnDisagreement.empty());

//     focusUsingSignDisagreements(errorVar, sgn);
//     d_sgnDisagreement.clear();
//     return 0;
//   }else if(selected.d_degenerate){
//     if(d_prevPivotImprovement == HeuristicDegenerate && 
//        d_pivotImprovementInARow >= s_focusThreshold){
      
//       d_errorSet.focusDownToJust(errorVar);
//       d_sgnDisagreement.clear();
//       return 0;
//     }
//   }

//   d_sgnDisagreement.clear();
//   updateAndSignal(selected);
//   logPivot(selected);

//   return selected.d_errorsFixed;
// }

// Result::Sat FCSimplexDecisionProcedure::dualLike(){
//   const static bool verbose = true;
//   static int instance = 0;

//   while(d_pivotBudget != 0  && d_errorSize > 0 && !d_conflictVariables.empty()){
//     ++instance;
//     Debug("dualLike") << "dualLike " << instance << endl;

//     Assert(d_errorSet.noSignals());

//     if(d_focusSize == 0){
//       d_errorSet.blur();
//     }else{
//       uint32_t prevFocusSize = d_focusSize;
//       uint32_t dropped;
//       ArithVar e = d_errorSet.topFocusVariable();

//       // Possible outcomes:
//       // - errorSet size shrunk
//       // -- fixed v
//       // -- fixed something other than v
//       // - conflict
//       // - budget was exhausted
//       // (dualLike only) focus went down
//       if(d_focusSize){
//         dropped = primalImproveError(e);
//       }else{
//         Assert(d_focusSize > 1);
//         dropped = dualLikeImproveError(e);
//       }

//       if(verbose){
//         if(!d_conflictVariables.empty()){
//           cout << "found conflict" << endl;
//         }else if(d_pivotBudget == 0){
//           cout << "budget exhausted" << endl;
//         }else if(dropped > 0){
//           cout << "dropped " << dropped << endl;
//         }else if(d_focusSize < prevFocusSize){
//           // focus went down
//           cout << "focus went down" << endl;
//         }else{
//           cout << "dualLikeImproveError pivot" << endl;
//         }
//       }
//     }
//   }

//   if(!d_conflictVariables.empty()){
//     return Result::UNSAT;
//   }else if(d_errorSet.errorEmpty()){
//     Assert(d_errorSet.noSignals());
//     return Result::SAT;
//   }else{
//     Assert(d_pivotBudget == 0);
//     return Result::SAT_UNKNOWN;      
//   }
// }

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
