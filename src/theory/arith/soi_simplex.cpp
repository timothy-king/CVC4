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


#include "theory/arith/soi_simplex.h"
#include "theory/arith/options.h"
#include "theory/arith/constraint.h"

#include "util/statistics_registry.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {


SumOfInfeasibilitiesSPD::SumOfInfeasibilitiesSPD(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
  , d_pivotBudget(0)
  , d_prevWitnessImprovement(AntiProductive)
  , d_witnessImprovementInARow(0)
  , d_sgnDisagreements()
  , d_statistics(d_pivots)
{ }

SumOfInfeasibilitiesSPD::Statistics::Statistics(uint32_t& pivots):
  d_initialSignalsTime("theory::arith::SOI::initialProcessTime"),
  d_initialConflicts("theory::arith::SOI::UpdateConflicts", 0),
  d_soiFoundUnsat("theory::arith::SOI::FoundUnsat", 0),
  d_soiFoundSat("theory::arith::SOI::FoundSat", 0),
  d_soiMissed("theory::arith::SOI::Missed", 0),
  d_soiTimer("theory::arith::SOI::Timer"),
  d_soiFocusConstructionTimer("theory::arith::SOI::Construction"),
  d_selectUpdateForSOI("theory::arith::SOI::selectSOI"),
  d_finalCheckPivotCounter("theory::arith::SOI::lastPivots", pivots)
{
  StatisticsRegistry::registerStat(&d_initialSignalsTime);
  StatisticsRegistry::registerStat(&d_initialConflicts);

  StatisticsRegistry::registerStat(&d_soiFoundUnsat);
  StatisticsRegistry::registerStat(&d_soiFoundSat);
  StatisticsRegistry::registerStat(&d_soiMissed);

  StatisticsRegistry::registerStat(&d_soiTimer);
  StatisticsRegistry::registerStat(&d_soiFocusConstructionTimer);

  StatisticsRegistry::registerStat(&d_selectUpdateForSOI);

  StatisticsRegistry::registerStat(&d_finalCheckPivotCounter);
}

SumOfInfeasibilitiesSPD::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_initialSignalsTime);
  StatisticsRegistry::unregisterStat(&d_initialConflicts);

  StatisticsRegistry::unregisterStat(&d_soiFoundUnsat);
  StatisticsRegistry::unregisterStat(&d_soiFoundSat);
  StatisticsRegistry::unregisterStat(&d_soiMissed);

  StatisticsRegistry::unregisterStat(&d_soiTimer);
  StatisticsRegistry::unregisterStat(&d_soiFocusConstructionTimer);

  StatisticsRegistry::unregisterStat(&d_selectUpdateForSOI);
  StatisticsRegistry::unregisterStat(&d_finalCheckPivotCounter);
}

Result::Sat SumOfInfeasibilitiesSPD::findModel(bool exactResult){
  Assert(d_conflictVariables.empty());
  Assert(d_sgnDisagreements.empty());

  d_pivots = 0;
  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;
  static const bool verbose = false;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Debug("arith::findModel") << "fcFindModel("<< instance <<") trivial" << endl;
    Assert(d_conflictVariables.empty());
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();

  // We must start tracking NOW
  d_errorSet.setSelectionRule(SUM_METRIC);

  if(initialProcessSignals()){
    d_conflictVariables.purge();
    if(verbose){ Message() << "fcFindModel("<< instance <<") early conflict" << endl; }
    Debug("arith::findModel") << "fcFindModel("<< instance <<") early conflict" << endl;
    Assert(d_conflictVariables.empty());
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Debug("arith::findModel") << "fcFindModel("<< instance <<") fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    Assert(d_conflictVariables.empty());
    return Result::SAT;
  }

  Debug("arith::findModel") << "fcFindModel(" << instance <<") start non-trivial" << endl;

  exactResult |= options::arithStandardCheckVarOrderPivots() < 0;

  d_prevWitnessImprovement = HeuristicDegenerate;
  d_witnessImprovementInARow = 0;

  Result::Sat result = Result::SAT_UNKNOWN;

  if(result == Result::SAT_UNKNOWN){
    if(exactResult){
      d_pivotBudget = -1;
    }else{
      d_pivotBudget = options::arithStandardCheckVarOrderPivots();
    }

    result = sumOfInfeasibilities();

    if(result ==  Result::UNSAT){
      ++(d_statistics.d_soiFoundUnsat);
      if(verbose){ Message() << "fc found unsat";}
    }else if(d_errorSet.errorEmpty()){
      ++(d_statistics.d_soiFoundSat);
      if(verbose){ Message() << "fc found model"; }
    }else{
      ++(d_statistics.d_soiMissed);
      if(verbose){ Message() << "fc missed"; }
    }
  }
  if(verbose){
    Message() << "(" << instance << ") pivots " << d_pivots << endl;
  }

  Assert(!d_errorSet.moreSignals());
  if(result == Result::SAT_UNKNOWN && d_errorSet.errorEmpty()){
    result = Result::SAT;
  }

  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Debug("arith::findModel") << "end findModel() " << instance << " " << result <<  endl;

  Assert(d_conflictVariables.empty());
  return result;
}


void SumOfInfeasibilitiesSPD::logPivot(WitnessImprovement w){
  if(d_pivotBudget > 0) {
    --d_pivotBudget;
  }
  Assert(w != AntiProductive);

  if(w == d_prevWitnessImprovement){
    ++d_witnessImprovementInARow;
    if(d_witnessImprovementInARow == 0){
      --d_witnessImprovementInARow;
    }
  }else{
    if(w != BlandsDegenerate){
      d_witnessImprovementInARow = 1;
    }
    d_prevWitnessImprovement = w;
  }
  if(strongImprovement(w)){
    d_leavingCountSinceImprovement.purge();
  }

  Debug("logPivot") << "logPivot " << d_prevWitnessImprovement << " "  << d_witnessImprovementInARow << endl;
}

uint32_t SumOfInfeasibilitiesSPD::degeneratePivotsInARow() const {
  switch(d_prevWitnessImprovement){
  case ConflictFound:
  case ErrorDropped:
  case FocusImproved:
    return 0;
  case HeuristicDegenerate:
  case BlandsDegenerate:
    return d_witnessImprovementInARow;
  // Degenerate is unreachable for its own reasons
  case Degenerate:
  case FocusShrank:
  case AntiProductive:
    Unreachable();
    return -1;
  }
  Unreachable();
}

void SumOfInfeasibilitiesSPD::adjustFocusAndError(const UpdateInfo& up, const AVIntPairVec& focusChanges){
  uint32_t newErrorSize = d_errorSet.errorSize();
  adjustInfeasFunc(d_statistics.d_soiFocusConstructionTimer, d_soiVar, focusChanges);

  d_errorSize = newErrorSize;
}

// void SumOfInfeasibilitiesSPD::adjustFocusAndError(const UpdateInfo& up, const AVIntPairVec& focusChanges){
//   uint32_t newErrorSize = d_errorSet.errorSize();
//   uint32_t newFocusSize = d_errorSet.focusSize();

//   //Assert(!d_conflictVariables.empty() || newFocusSize <= d_focusSize);
//   Assert(!d_conflictVariables.empty() || newErrorSize <= d_errorSize);

//   if(newFocusSize == 0 || !d_conflictVariables.empty() ){
//     tearDownFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
//   }else if(2*newFocusSize < d_focusSize ){
//     tearDownFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
//     constructFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
//   }else{
//     adjustFocusFunction(d_statistics.d_fcFocusConstructionTimer, focusChanges);
//   }

//   d_errorSize = newErrorSize;
//   d_focusSize = newFocusSize;
// }

// WitnessImprovement SumOfInfeasibilitiesSPD::adjustFocusShrank(const ArithVarVec& dropped){
//   Assert(dropped.size() > 0);
//   Assert(d_errorSet.focusSize() == d_focusSize);
//   Assert(d_errorSet.focusSize() > dropped.size());

//   uint32_t newFocusSize = d_focusSize - dropped.size();
//   Assert(newFocusSize > 0);

//   if(2 * newFocusSize <= d_focusSize){
//     d_errorSet.dropFromFocusAll(dropped);
//     tearDownFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
//     constructFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
//   }else{
//     shrinkFocusFunction(d_statistics.d_fcFocusConstructionTimer, dropped);
//     d_errorSet.dropFromFocusAll(dropped);
//   }

//   d_focusSize = newFocusSize;
//   Assert(d_errorSet.focusSize() == d_focusSize);
//   return FocusShrank;
// }

// WitnessImprovement SumOfInfeasibilitiesSPD::focusDownToJust(ArithVar v){
//   // uint32_t newErrorSize = d_errorSet.errorSize();
//   // uint32_t newFocusSize = d_errorSet.focusSize();
//   Assert(d_focusSize ==  d_errorSet.focusSize());
//   Assert(d_focusSize > 1);
//   Assert(d_errorSet.inFocus(v));

//   d_errorSet.focusDownToJust(v);
//   Assert(d_errorSet.focusSize() == 1);
//   d_focusSize = 1;

//   tearDownFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
//   constructFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);

//   return FocusShrank;
// }



UpdateInfo SumOfInfeasibilitiesSPD::selectUpdate(LinearEqualityModule::UpdatePreferenceFunction upf, LinearEqualityModule::VarPreferenceFunction bpf) {
  UpdateInfo selected;

  static int instance = 0 ;
  ++instance;

  ArithVar basic = d_soiVar;

  Debug("arith::selectPrimalUpdate")
    << "selectPrimalUpdate " << instance << endl
    << basic << " " << d_tableau.basicRowLength(basic)
    << " " << d_linEq._countBounds(basic) << endl;

  typedef std::vector<Cand> CandVector;
  CandVector candidates;

  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(basic); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    if(curr == basic){ continue; }

    int sgn = e.getCoefficient().sgn();
    static const int basicDir = 1;
    int curr_movement = basicDir * sgn;

    bool candidate =
      (curr_movement > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
      (curr_movement < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0);

    Debug("arith::selectPrimalUpdate")
      << "storing " << basic
      << " " << curr
      << " " << candidate
      << " " << e.getCoefficient()
      << " " << curr_movement << endl;

    if(!candidate) { continue; }

    // if(!isFocus){
    //   const Rational& focusC = focusCoefficient(curr);
    //   Assert(dualLike || !focusC.isZero());
    //   if(dualLike && curr_movement != focusC.sgn()){
    //     Debug("arith::selectPrimalUpdate") << "sgn disagreement " << curr << endl;
    //     d_sgnDisagreements.push_back(curr);
    //     continue;
    //   }else{
    //     candidates.push_back(Cand(curr, penalty(curr), curr_movement, &focusC));
    //   }
    // }else{
    //  candidates.push_back(Cand(curr, penalty(curr), curr_movement, &e.getCoefficient()));
    candidates.push_back(Cand(curr, 0, curr_movement, &e.getCoefficient()));
    // }
  }

  CompPenaltyColLength colCmp(&d_linEq);
  CandVector::iterator i = candidates.begin();
  CandVector::iterator end = candidates.end();
  std::make_heap(i, end, colCmp);

  // For the first 3 pivots take the best
  // After that, once an improvement is found on look at a
  // small number of pivots after finding an improvement
  // the longer the search to more willing we are to look at more candidates
  int maxCandidatesAfterImprove =
    (d_pivots <= 2) ?  std::numeric_limits<int>::max() : d_pivots/5;

  int candidatesAfterFocusImprove = 0;
  while(i != end && candidatesAfterFocusImprove <= maxCandidatesAfterImprove){
    std::pop_heap(i, end, colCmp);
    --end;
    Cand& cand = (*end);
    ArithVar curr = cand.d_nb;
    const Rational& coeff = *cand.d_coeff;

#warning "Who is using computeSafeUpdate?"
    LinearEqualityModule::UpdatePreferenceFunction leavingPrefFunc = selectLeavingFunction(curr);
    UpdateInfo currProposal = d_linEq.speculativeUpdate(curr, coeff, leavingPrefFunc);

    Debug("arith::selectPrimalUpdate")
      << "selected " << selected << endl
      << "currProp " << currProposal << endl
      << "coeff " << coeff << endl;

    Assert(!currProposal.uninitialized());

    if(candidatesAfterFocusImprove > 0){
      candidatesAfterFocusImprove++;
    }

    if(selected.uninitialized() || (d_linEq.*upf)(selected, currProposal)){
      selected = currProposal;
      WitnessImprovement w = selected.getWitness(false);
      Debug("arith::selectPrimalUpdate") << "selected " << w << endl;
      //setPenalty(curr, w);
      if(improvement(w)){
        bool exitEarly;
        switch(w){
        case ConflictFound: exitEarly = true; break;
        case FocusImproved:
          candidatesAfterFocusImprove = 1;
          exitEarly = false;
          break;
        default:
          exitEarly = false; break;
        }
        if(exitEarly){ break; }
      }
    }else{
      Debug("arith::selectPrimalUpdate") << "dropped "<< endl;
    }

  }

  // if(!isFocus){
  //   unloadFocusSigns();
  // }
  return selected;
}

bool debugCheckWitness(const UpdateInfo& inf, WitnessImprovement w, bool useBlands){
  if(inf.getWitness(useBlands) == w){
    switch(w){
    case ConflictFound: return inf.foundConflict();
    case ErrorDropped: return inf.errorsChange() < 0;
    case FocusImproved: return inf.focusDirection() > 0;
    case FocusShrank: return false; // This is not a valid output
    case Degenerate: return false; // This is not a valid output
    case BlandsDegenerate: return useBlands;
    case HeuristicDegenerate: return !useBlands;
    case AntiProductive: return false;
    }
  }
  return false;
}

// WitnessImprovement SumOfInfeasibilitiesSPD::primalImproveError(ArithVar errorVar){
//   bool useBlands = degeneratePivotsInARow() >= s_maxDegeneratePivotsBeforeBlandsOnLeaving;
//   UpdateInfo selected = selectUpdateForPrimal (errorVar, useBlands);
//   Assert(!selected.uninitialized());
//   WitnessImprovement w = selected.getWitness(useBlands);
//   Assert(debugCheckWitness(selected, w, useBlands));

//   updateAndSignal(selected, w);
//   logPivot(w);
//   return w;
// }


// WitnessImprovement SumOfInfeasibilitiesSPD::focusUsingSignDisagreements(ArithVar basic){
//   Assert(!d_sgnDisagreements.empty());
//   Assert(d_errorSet.focusSize() >= 2);

//   if(Debug.isOn("arith::focus")){
//     d_errorSet.debugPrint(Debug("arith::focus"));
//   }

//   ArithVar nb = d_linEq.minBy(d_sgnDisagreements, &LinearEqualityModule::minColLength);
//   const Tableau::Entry& e_evar_nb = d_tableau.basicFindEntry(basic, nb);
//   int oppositeSgn = - (e_evar_nb.getCoefficient().sgn());
//   Debug("arith::focus") << "focusUsingSignDisagreements " << basic << " " << oppositeSgn << endl;

//   ArithVarVec dropped;

//   Tableau::ColIterator colIter = d_tableau.colIterator(nb);
//   for(; !colIter.atEnd(); ++colIter){
//     const Tableau::Entry& entry = *colIter;
//     Assert(entry.getColVar() == nb);

//     int sgn = entry.getCoefficient().sgn();
//     Debug("arith::focus")
//       << "on row "
//       << d_tableau.rowIndexToBasic(entry.getRowIndex())
//       << " "
//       << entry.getCoefficient() << endl;
//     ArithVar currRow = d_tableau.rowIndexToBasic(entry.getRowIndex());
//     if(d_errorSet.inError(currRow) && d_errorSet.inFocus(currRow)){
//       int errSgn = d_errorSet.getSgn(currRow);

//       if(errSgn * sgn == oppositeSgn){
//         dropped.push_back(currRow);
//         Debug("arith::focus") << "dropping from focus " << currRow << endl;
//       }
//     }
//   }

//   d_sgnDisagreements.clear();
//   return adjustFocusShrank(dropped);
// }

// bool debugSelectedErrorDropped(const UpdateInfo& selected, int32_t prevErrorSize, int32_t currErrorSize){
//   int diff = currErrorSize - prevErrorSize;
//   return selected.foundConflict() || diff == selected.errorsChange();
// }

void SumOfInfeasibilitiesSPD::debugPrintSignal(ArithVar updated) const{
  Debug("updateAndSignal") << "updated basic " << updated;
  Debug("updateAndSignal") << " length " << d_tableau.basicRowLength(updated);
  Debug("updateAndSignal") << " consistent " << d_variables.assignmentIsConsistent(updated);
  int dir = !d_variables.assignmentIsConsistent(updated) ?
    d_errorSet.getSgn(updated) : 0;
  Debug("updateAndSignal") << " dir " << dir;
  Debug("updateAndSignal") << " _countBounds " << d_linEq._countBounds(updated) << endl;
}

// bool debugUpdatedBasic(const UpdateInfo& selected, ArithVar updated){
//   if(selected.describesPivot() &&  updated == selected.leaving()){
//     return selected.foundConflict();
//   }else{
//     return true;
//   }
// }

void SumOfInfeasibilitiesSPD::updateAndSignal(const UpdateInfo& selected, WitnessImprovement w){
  ArithVar nonbasic = selected.nonbasic();

  static bool verbose = false;

  Debug("updateAndSignal") << "updateAndSignal " << selected << endl;

  stringstream ss;
  if(verbose){
    d_errorSet.debugPrint(ss);
    if(selected.describesPivot()){
      ArithVar leaving = selected.leaving();
      ss << "leaving " << leaving
         << " " << d_tableau.basicRowLength(leaving)
         << " " << d_linEq._countBounds(leaving)
         << endl;
    }
    if(degenerate(w) && selected.describesPivot()){
      ArithVar leaving = selected.leaving();
      Message()
        << "degenerate " << leaving
        << ", atBounds " << d_linEq.basicsAtBounds(selected)
        << ", len " << d_tableau.basicRowLength(leaving)
        << ", bc " << d_linEq._countBounds(leaving)
        << endl;
    }
  }

  if(selected.describesPivot()){
    Constraint limiting = selected.limiting();
    ArithVar basic = limiting->getVariable();
    Assert(d_linEq.basicIsTracked(basic));
    d_linEq.pivotAndUpdate(basic, nonbasic, limiting->getValue());
  }else{
    Assert(!selected.unbounded() || selected.errorsChange() < 0);

    DeltaRational newAssignment =
      d_variables.getAssignment(nonbasic) + selected.nonbasicDelta();

    d_linEq.updateTracked(nonbasic, newAssignment);
  }
  d_pivots++;

  increaseLeavingCount(nonbasic);

  vector< pair<ArithVar, int> > focusChanges;
  while(d_errorSet.moreSignals()){
    ArithVar updated = d_errorSet.topSignal();
    int prevFocusSgn = d_errorSet.popSignal();

    if(d_tableau.isBasic(updated)){
      Assert(!d_variables.assignmentIsConsistent(updated) == d_errorSet.inError(updated));
      if(Debug.isOn("updateAndSignal")){debugPrintSignal(updated);}
      if(!d_variables.assignmentIsConsistent(updated)){
        if(checkBasicForConflict(updated)){
          reportConflict(updated);
          //Assert(debugUpdatedBasic(selected, updated));
        }
      }
    }else{
      Debug("updateAndSignal") << "updated nonbasic " << updated << endl;
    }
    int currFocusSgn = d_errorSet.focusSgn(updated);
    if(currFocusSgn != prevFocusSgn){
      int change = currFocusSgn - prevFocusSgn;
      focusChanges.push_back(make_pair(updated, change));
    }
  }

  if(verbose){
    Message() << "conflict variable " << selected << endl;
    Message() << ss.str();
  }
  if(Debug.isOn("error")){ d_errorSet.debugPrint(Debug("error")); }

  //Assert(debugSelectedErrorDropped(selected, d_errorSize, d_errorSet.errorSize()));

  adjustFocusAndError(selected, focusChanges);
}

// WitnessImprovement SumOfInfeasibilitiesSPD::soiRound(){
//   Assert(d_sgnDisagreements.empty());
//   Assert(d_focusSize > 1);

//   UpdateInfo selected = selectUpdateForDualLike(errorVar);

//   if(selected.uninitialized()){
//     // we found no proposals
//     // If this is empty, there must be an error on this variable!
//     // this should not be possible. It Should have been caught as a signal earlier
//     WitnessImprovement dropped = focusUsingSignDisagreements(errorVar);
//     Assert(d_sgnDisagreements.empty());

//     return dropped;
//   }else{
//     d_sgnDisagreements.clear();
//   }

//   Assert(d_sgnDisagreements.empty());
//   Assert(!selected.uninitialized());

//   if(selected.focusDirection() == 0 &&
//      d_prevWitnessImprovement == HeuristicDegenerate &&
//      d_witnessImprovementInARow >= s_focusThreshold){

//     Debug("focusDownToJust") << "focusDownToJust " << errorVar << endl;

//     return focusDownToJust(errorVar);
//   }else{
//     WitnessImprovement w = selected.getWitness(false);
//     Assert(debugCheckWitness(selected, w, false));
//     updateAndSignal(selected, w);
//     logPivot(w);
//     return w;
//   }

// }

// WitnessImprovement SumOfInfeasibilitiesSPD::dualLikeImproveError(ArithVar errorVar){
//   Assert(d_sgnDisagreements.empty());
//   Assert(d_focusSize > 1);

//   UpdateInfo selected = selectUpdateForDualLike(errorVar);

//   if(selected.uninitialized()){
//     // we found no proposals
//     // If this is empty, there must be an error on this variable!
//     // this should not be possible. It Should have been caught as a signal earlier
//     WitnessImprovement dropped = focusUsingSignDisagreements(errorVar);
//     Assert(d_sgnDisagreements.empty());

//     return dropped;
//   }else{
//     d_sgnDisagreements.clear();
//   }

//   Assert(d_sgnDisagreements.empty());
//   Assert(!selected.uninitialized());

//   if(selected.focusDirection() == 0 &&
//      d_prevWitnessImprovement == HeuristicDegenerate &&
//      d_witnessImprovementInARow >= s_focusThreshold){

//     Debug("focusDownToJust") << "focusDownToJust " << errorVar << endl;

//     return focusDownToJust(errorVar);
//   }else{
//     WitnessImprovement w = selected.getWitness(false);
//     Assert(debugCheckWitness(selected, w, false));
//     updateAndSignal(selected, w);
//     logPivot(w);
//     return w;
//   }
// }

// WitnessImprovement SumOfInfeasibilitiesSPD::focusDownToLastHalf(){
//   Assert(d_focusSize >= 2);

//   Debug("focusDownToLastHalf") << "focusDownToLastHalf "
//        << d_errorSet.errorSize()  << " "
//        << d_errorSet.focusSize() << " ";

//   uint32_t half = d_focusSize/2;
//   ArithVarVec buf;
//   for(ErrorSet::focus_iterator i = d_errorSet.focusBegin(),
//         i_end = d_errorSet.focusEnd(); i != i_end; ++i){
//     if(half > 0){
//       --half;
//     } else{
//       buf.push_back(*i);
//     }
//   }

//   Debug("focusDownToLastHalf") << "-> " << d_errorSet.focusSize() << endl;

//   return adjustFocusShrank(buf);
// }

WitnessImprovement SumOfInfeasibilitiesSPD::SOIConflict(){
  static int instance = 0;
  instance++;
  cout << "SOI conflict " << instance << endl;
  NodeBuilder<> conflict(kind::AND);
  for(ErrorSet::focus_iterator iter = d_errorSet.focusBegin(), end = d_errorSet.focusEnd(); iter != end; ++iter){
    ArithVar e = *iter;
    Constraint violated = d_errorSet.getViolated(e);
    cout << "basic error var: " << violated << endl;
    violated->explainForConflict(conflict);
  }
  for(Tableau::RowIterator i = d_tableau.basicRowIterator(d_soiVar); !i.atEnd(); ++i){
    const Tableau::Entry& entry = *i;
    ArithVar v = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();

    Constraint c = (coeff.sgn() > 0) ?
      d_variables.getUpperBoundConstraint(v) :
      d_variables.getLowerBoundConstraint(v);

    cout << "nb : " << c << endl;
    c->explainForConflict(conflict);
  }

  Node conf = conflict;
  //reportConflict(conf); do not do this. We need a custom explaination
  d_conflictVariables.add(d_soiVar);
  d_conflictChannel(conf);
  cout << "SOI conflict " << instance << "end" << endl;
}

WitnessImprovement SumOfInfeasibilitiesSPD::soiRound() {
  Assert(d_soiVar != ARITHVAR_SENTINEL);

  bool useBlands = degeneratePivotsInARow() >= s_maxDegeneratePivotsBeforeBlandsOnLeaving;
  LinearEqualityModule::UpdatePreferenceFunction upf = useBlands ?
    &LinearEqualityModule::preferWitness<false>:
    &LinearEqualityModule::preferWitness<true>;

  LinearEqualityModule::VarPreferenceFunction bpf = useBlands ?
    &LinearEqualityModule::minVarOrder :
    &LinearEqualityModule::minRowLength;
  bpf = &LinearEqualityModule::minVarOrder;

  UpdateInfo selected = selectUpdate(upf, bpf);

  if(selected.uninitialized()){
    Debug("selectFocusImproving") << "SOI is optimum, but we don't have sat/conflict yet" << endl;
    return SOIConflict();
  }else{
    Assert(!selected.uninitialized());
    WitnessImprovement w = selected.getWitness(false);
    Assert(debugCheckWitness(selected, w, false));

    updateAndSignal(selected, w);
    logPivot(w);
    return w;
  }
}

bool SumOfInfeasibilitiesSPD::debugSOI(WitnessImprovement w, ostream& out, int instance) const{
  return false;
  // out << "DLV("<<instance<<") ";
  // switch(w){
  // case ConflictFound:
  //   out << "found conflict" << endl;
  //   return !d_conflictVariables.empty();
  // case ErrorDropped:
  //   return false;
  //   // out << "dropped " << prevErrorSize - d_errorSize << endl;
  //   // return d_errorSize < prevErrorSize;
  // case FocusImproved:
  //   out << "focus improved"<< endl;
  //   return d_errorSize == prevErrorSize;
  // case FocusShrank:
  //   Unreachable();
  //   return false;
  // case BlandsDegenerate:
  //   out << "bland degenerate"<< endl;
  //   return true;
  // case HeuristicDegenerate:
  //   out << "heuristic degenerate"<< endl;
  //   return true;
  // case AntiProductive:
  // case Degenerate:
  //   return false;
  // }
  // return false;
}

Result::Sat SumOfInfeasibilitiesSPD::sumOfInfeasibilities(){
  static int instance = 0;
  static bool verbose = false;

  TimerStat::CodeTimer codeTimer(d_statistics.d_soiTimer);

  Assert(d_sgnDisagreements.empty());
  Assert(d_pivotBudget != 0);
  Assert(d_errorSize == d_errorSet.errorSize());
  Assert(d_errorSize > 0);
  Assert(d_conflictVariables.empty());
  Assert(d_soiVar == ARITHVAR_SENTINEL);


  //d_scores.purge();
  d_soiVar = constructInfeasiblityFunction(d_statistics.d_soiFocusConstructionTimer);


  while(d_pivotBudget != 0  && d_errorSize > 0 && d_conflictVariables.empty()){
    ++instance;
    Debug("dualLike") << "dualLike " << instance << endl;

    Assert(d_errorSet.noSignals());
    // Possible outcomes:
    // - conflict
    // - budget was exhausted
    // - focus went down
    Debug("dualLike") << "selectFocusImproving " << endl;
    WitnessImprovement w = soiRound();

    Assert(d_errorSize == d_errorSet.errorSize());

    if(verbose){
      debugSOI(w,  Message(), instance);
    }
    Assert(debugSOI(w, Debug("dualLike"), instance));
  }


  if(d_soiVar != ARITHVAR_SENTINEL){
    tearDownInfeasiblityFunction(d_statistics.d_soiFocusConstructionTimer, d_soiVar);
  }

  Assert(d_soiVar == ARITHVAR_SENTINEL);
  if(!d_conflictVariables.empty()){
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Assert(d_errorSet.noSignals());
    return Result::SAT;
  }else{
    Assert(d_pivotBudget == 0);
    return Result::SAT_UNKNOWN;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
