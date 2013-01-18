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


#include "theory/arith/fc_simplex.h"
#include "theory/arith/options.h"
#include "theory/arith/constraint.h"

#include "util/statistics_registry.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {


FCSimplexDecisionProcedure::FCSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
  , d_pivotBudget(0)
  , d_prevWitnessImprovement(AntiProductive)
  , d_witnessImprovementInARow(0)
  , d_sgnDisagreements()
  , d_statistics()
{ }

FCSimplexDecisionProcedure::Statistics::Statistics():
  d_initialSignalsTime("theory::arith::FC::initialProcessTime"),
  d_initialConflicts("theory::arith::FC::UpdateConflicts", 0),
  d_fcFoundUnsat("theory::arith::FC::FoundUnsat", 0),
  d_fcFoundSat("theory::arith::FC::FoundSat", 0),
  d_fcMissed("theory::arith::FC::Missed", 0),
  d_fcTimer("theory::arith::FC::Timer"),
  d_fcFocusConstructionTimer("theory::arith::FC::Construction"),
  d_selectUpdateForDualLike("theory::arith::FC::selectUpdateForDualLike"),
  d_selectUpdateForPrimal("theory::arith::FC::selectUpdateForPrimal")
{
  StatisticsRegistry::registerStat(&d_initialSignalsTime);
  StatisticsRegistry::registerStat(&d_initialConflicts);

  StatisticsRegistry::registerStat(&d_fcFoundUnsat);
  StatisticsRegistry::registerStat(&d_fcFoundSat);
  StatisticsRegistry::registerStat(&d_fcMissed);

  StatisticsRegistry::registerStat(&d_fcTimer);
  StatisticsRegistry::registerStat(&d_fcFocusConstructionTimer);

  StatisticsRegistry::registerStat(&d_selectUpdateForDualLike);
  StatisticsRegistry::registerStat(&d_selectUpdateForPrimal);
}

FCSimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_initialSignalsTime);
  StatisticsRegistry::unregisterStat(&d_initialConflicts);

  StatisticsRegistry::unregisterStat(&d_fcFoundUnsat);
  StatisticsRegistry::unregisterStat(&d_fcFoundSat);
  StatisticsRegistry::unregisterStat(&d_fcMissed);

  StatisticsRegistry::unregisterStat(&d_fcTimer);
  StatisticsRegistry::unregisterStat(&d_fcFocusConstructionTimer);

  StatisticsRegistry::unregisterStat(&d_selectUpdateForDualLike);
  StatisticsRegistry::unregisterStat(&d_selectUpdateForPrimal);
}

Result::Sat FCSimplexDecisionProcedure::findModel(bool exactResult){
  Assert(d_conflictVariables.empty());
  Assert(d_sgnDisagreements.empty());

  d_pivots = 0;
  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;

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

  static const bool verbose = false;
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

    result = dualLike();

    if(result ==  Result::UNSAT){
      ++(d_statistics.d_fcFoundUnsat);
      if(verbose){ Message() << "fc found unsat";}
    }else if(d_errorSet.errorEmpty()){
      ++(d_statistics.d_fcFoundSat);
      if(verbose){ Message() << "fc found model"; }
    }else{
      ++(d_statistics.d_fcMissed);
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


void FCSimplexDecisionProcedure::logPivot(const UpdateInfo& selected, bool useBlands){
  if(d_pivotBudget > 0) {
    --d_pivotBudget;
  }
  WitnessImprovement curr = selected.getWitness(useBlands);

  Assert(curr != AntiProductive);

  if(curr == d_prevWitnessImprovement){
    ++d_witnessImprovementInARow;
    if(d_witnessImprovementInARow == 0){
      --d_witnessImprovementInARow;
    }
  }else{
    d_prevWitnessImprovement = curr;
    if(d_prevWitnessImprovement != HeuristicDegenerate){
      d_witnessImprovementInARow = 1;
    }
  }
  Debug("logPivot") << "logPivot " << d_prevWitnessImprovement << " "  << d_witnessImprovementInARow << ": " << selected << endl;
}

uint32_t FCSimplexDecisionProcedure::degeneratePivotsInARow() const {
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
  case AntiProductive:
    Unreachable();
    return -1;
  }
  Unreachable();
}

void FCSimplexDecisionProcedure::adjustFocusAndError(bool readjust){
  uint32_t newErrorSize = d_errorSet.errorSize();
  uint32_t newFocusSize = d_errorSet.focusSize();

  Assert(!d_conflictVariables.empty() || newFocusSize <= d_focusSize);
  Assert(!d_conflictVariables.empty() || newErrorSize <= d_errorSize);
  if( newFocusSize == 0 ){
    tearDownFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
  }else if(readjust || newFocusSize < d_focusSize){
    reconstructFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
  }
  d_errorSize = newErrorSize;
  d_focusSize = newFocusSize;
}



UpdateInfo FCSimplexDecisionProcedure::selectPrimalUpdate(ArithVar basic, LinearEqualityModule::UpdatePreferenceFunction upf, LinearEqualityModule::VarPreferenceFunction bpf) {
  UpdateInfo currProposal;
  UpdateInfo selected;

  static int instance = 0 ;
  ++instance;

  Debug("arith::selectPrimalUpdate")
    << "selectPrimalUpdate " << instance << endl
    << basic << " " << d_tableau.basicRowLength(basic)
    << " " << d_linEq._countBounds(basic) << endl;

  static const int s_maxCandidatesAfterImprove = 3;
  bool isFocus = basic == d_focusErrorVar;
  Assert(isFocus || d_errorSet.inError(basic));
  int basicDir =  isFocus? 1 : d_errorSet.getSgn(basic);
  bool dualLike = !isFocus && d_focusSize > 1;

  if(dualLike){
    loadFocusSigns();
  }

  typedef std::vector<Cand> CandVector;
  CandVector candidates;

  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(basic); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    if(curr == basic){ continue; }

    int sgn = e.getCoefficient().sgn();
    int curr_movement = basicDir * sgn;

    bool candidate =
      (curr_movement > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
      (curr_movement < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0);

    Debug("arith::selectPrimalUpdate")
      << "storing " << basic
      << " " << curr
      << " " << candidate
      << " " << e.getCoefficient()
      << " " << curr_movement
      << " " << focusSgn(curr) << endl;

    if(!candidate) { continue; }

    if(dualLike && curr_movement != focusSgn(curr)){
      Debug("arith::selectPrimalUpdate") << "sgn disagreement " << curr << endl;
      d_sgnDisagreements.push_back(curr);
      continue;
    }else{
      candidates.push_back(Cand(curr, curr_movement, &e.getCoefficient()));
    }
  }

  CompColLength colCmp(&d_linEq);
  CandVector::iterator i = candidates.begin();
  CandVector::iterator end = candidates.end();
  std::make_heap(i, end, colCmp);

  bool checkEverything = d_pivots == 0;

  int candidatesAfterFocusImprove = 0;
  while(i != end && (checkEverything || candidatesAfterFocusImprove <= s_maxCandidatesAfterImprove)){
    std::pop_heap(i, end, colCmp);
    --end;
    Cand& cand = (*end);
    ArithVar curr = cand.d_nb;
    int curr_movement = cand.d_sgn;
    const Rational& coeff = *cand.d_coeff;

    if(isFocus){
      currProposal = d_linEq.speculativeUpdate(curr, coeff, upf);
    }else{
      currProposal = UpdateInfo(curr, curr_movement);
      d_linEq.computeSafeUpdate(currProposal, bpf);
    }

    Debug("arith::selectPrimalUpdate")
      << "selected " << selected << endl
      << "currProp " << currProposal << endl
      << "coeff " << coeff << endl;


    if(candidatesAfterFocusImprove > 0){
      candidatesAfterFocusImprove++;
    }

    if(selected.uninitialized() || (d_linEq.*upf)(selected, currProposal)){

      selected = currProposal;
      WitnessImprovement w = selected.getWitness(false);
      Debug("arith::selectPrimalUpdate") << "selected " << w << endl;

      if(improvement(w)){
        bool exitEarly;
        switch(w){
        case ConflictFound: exitEarly = true; break;
        case ErrorDropped:
          if(checkEverything){
            exitEarly = d_errorSize + selected.errorsChange() == 0;
            Debug("arith::selectPrimalUpdate")
              << "ee " << d_errorSize << " "
              << selected.errorsChange() << " "
              << d_errorSize + selected.errorsChange() << endl;
          }else{
            exitEarly = true;
          }
          break;
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

  if(dualLike){
    unloadFocusSigns();
  }
  return selected;
}

int FCSimplexDecisionProcedure::primalImproveError(ArithVar errorVar){
  bool useBlands = degeneratePivotsInARow() >= s_maxDegeneratePivotsBeforeBlands;
  UpdateInfo selected = selectUpdateForPrimal (errorVar, useBlands);
  Assert(!selected.uninitialized());
  updateAndSignal(selected);
  logPivot(selected, useBlands);

  Assert(selected.errorsChange() <= 0);

  return selected.errorsChange();
}


void FCSimplexDecisionProcedure::focusUsingSignDisagreements(ArithVar basic){
  Assert(!d_sgnDisagreements.empty());
  Assert(d_errorSet.focusSize() >= 2);

  if(Debug.isOn("arith::focus")){
    d_errorSet.debugPrint();
  }

  ArithVar nb = d_linEq.minBy(d_sgnDisagreements, &LinearEqualityModule::minColLength);
  const Tableau::Entry& e_evar_nb = d_tableau.basicFindEntry(basic, nb);
  int oppositeSgn = - (e_evar_nb.getCoefficient().sgn());
  Debug("arith::focus") << "focusUsingSignDisagreements " << basic << " " << oppositeSgn << endl;

  Tableau::ColIterator colIter = d_tableau.colIterator(nb);
  for(; !colIter.atEnd(); ++colIter){
    const Tableau::Entry& entry = *colIter;
    Assert(entry.getColVar() == nb);

    int sgn = entry.getCoefficient().sgn();
    Debug("arith::focus")
      << "on row "
      << d_tableau.rowIndexToBasic(entry.getRowIndex())
      << " "
      << entry.getCoefficient() << endl;
    ArithVar currRow = d_tableau.rowIndexToBasic(entry.getRowIndex());
    if(d_errorSet.inError(currRow) && d_errorSet.inFocus(currRow)){
      int errSgn = d_errorSet.getSgn(currRow);

      if(errSgn * sgn == oppositeSgn){
        d_errorSet.dropFromFocus(currRow);
        Debug("arith::focus") << "dropping from focus " << currRow << endl;
      }
    }
  }

  Assert(d_focusSize > d_errorSet.focusSize() );
  Assert(d_errorSet.focusSize() >= 1);
}

bool debugSelectedErrorDropped(const UpdateInfo& selected, int32_t prevErrorSize, int32_t currErrorSize){
  int diff = currErrorSize - prevErrorSize;
  return selected.foundConflict() || diff == selected.errorsChange();
}

void FCSimplexDecisionProcedure::updateAndSignal(const UpdateInfo& selected){
  ArithVar nonbasic = selected.nonbasic();

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
  d_errorSet.debugPrint();
  bool readjust = false;
  while(d_errorSet.moreSignals()){
    ArithVar updated = d_errorSet.topSignal();
    bool inError = d_errorSet.inError(updated);
    d_errorSet.popSignal();
    readjust |= inError == d_errorSet.inError(updated);

    if(d_tableau.isBasic(updated) &&
       !d_variables.assignmentIsConsistent(updated) &&
       checkBasicForConflict(updated)){
      reportConflict(updated);
    }
  }
  d_pivots++;

  d_errorSet.debugPrint();
  Assert(debugSelectedErrorDropped(selected, d_errorSize, d_errorSet.errorSize()));

  adjustFocusAndError(readjust);
}

int FCSimplexDecisionProcedure::dualLikeImproveError(ArithVar errorVar){
  Assert(d_sgnDisagreements.empty());

  int sgn = d_errorSet.getSgn(errorVar);
  UpdateInfo selected = selectUpdateForDualLike(errorVar, sgn);

  if(selected.uninitialized()){
    // we found no proposals
    // If this is empty, there must be an error on this variable!
    // this should not be possible. It Should have been caught as a signal earlier
    focusUsingSignDisagreements(errorVar);
  }

  d_sgnDisagreements.clear();
  Assert(d_sgnDisagreements.empty());

  if(selected.uninitialized()){
    // focus using sgn disagreement earlier
    Assert(d_focusSize > d_errorSet.focusSize());
    Assert(d_errorSet.focusSize() >= 1);
    adjustFocusAndError(false);
    return 0;
  }else if(selected.focusDirection() == 0 &&
           d_prevWitnessImprovement == HeuristicDegenerate &&
           d_witnessImprovementInARow >= s_focusThreshold){
    d_errorSet.focusDownToJust(errorVar);
    Assert(d_focusSize > d_errorSet.focusSize());
    Assert(d_errorSet.focusSize() == 1);
    adjustFocusAndError(false);
    return 0;
  }else{
    updateAndSignal(selected);
    logPivot(selected, false);
    Assert(selected.errorsChange() <= 0);
    return selected.errorsChange();
  }
}

void FCSimplexDecisionProcedure::focusDownToLastHalf(){
  Assert(d_focusSize >= 2);

  Debug("focusDownToLastHalf") << "focusDownToLastHalf "
       << d_errorSet.errorSize()  << " "
       << d_errorSet.focusSize() << " ";

  uint32_t half = d_focusSize/2;
  ArithVarVec buf;
  for(ErrorSet::focus_iterator i = d_errorSet.focusBegin(),
        i_end = d_errorSet.focusEnd(); i != i_end; ++i){
    if(half > 0){
      --half;
    } else{
      buf.push_back(*i);
    }
  }
  while(!buf.empty()){
    d_errorSet.dropFromFocus(buf.back());
    buf.pop_back();
  }

  Debug("focusDownToLastHalf") << "-> " << d_errorSet.focusSize() << endl;

}

bool FCSimplexDecisionProcedure::selectFocusImproving() {
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  Assert(d_focusSize >= 2);

  LinearEqualityModule::UpdatePreferenceFunction upf =
    &LinearEqualityModule::preferWitness<true>;

  LinearEqualityModule::VarPreferenceFunction bpf =
    &LinearEqualityModule::minRowLength;

  UpdateInfo selected = selectPrimalUpdate(d_focusErrorVar, upf, bpf);

  if(selected.uninitialized()){
    Debug("selectFocusImproving") << "focus is optimum, but we don't have sat/conflict yet" << endl;
    focusDownToLastHalf();
    adjustFocusAndError(false);
    return true;
  }
  Assert(!selected.uninitialized());
  Assert(selected.getWitness(true) < FocusImproved || selected.focusDirection() >= 0);
  if(!selected.foundConflict()){
    if(selected.focusDirection() == 0){
      Debug("selectFocusImproving") << "only degenerate" << endl;
      if(d_prevWitnessImprovement == HeuristicDegenerate &&
         d_witnessImprovementInARow >= s_focusThreshold){
        Debug("selectFocusImproving") << "focus down been degenerate too long" << endl;
        focusDownToLastHalf();
        adjustFocusAndError(false);
        return true;
      }else{
        Debug("selectFocusImproving") << "taking degenerate" << endl;
      }
    }
  }
  Debug("selectFocusImproving") << "selectFocusImproving did this " << selected << endl;

  updateAndSignal(selected);
  logPivot(selected, false);
  Assert(selected.foundConflict() || selected.errorsChange() <= 0);
  return false;
}

Result::Sat FCSimplexDecisionProcedure::dualLike(){
  const static bool verbose = false;
  static int instance = 0;

  TimerStat::CodeTimer codeTimer(d_statistics.d_fcTimer);

  Assert(d_sgnDisagreements.empty());
  Assert(d_pivotBudget != 0);
  Assert(d_errorSize == d_errorSet.errorSize());
  Assert(d_errorSize > 0);
  Assert(d_focusSize == d_errorSet.focusSize());
  Assert(d_focusSize > 0);
  Assert(d_conflictVariables.empty());
  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);

  constructFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);

  while(d_pivotBudget != 0  && d_errorSize > 0 && d_conflictVariables.empty()){
    ++instance;
    Debug("dualLike") << "dualLike " << instance << endl;

    Assert(d_errorSet.noSignals());

    int dropped = 0;
    uint32_t prevFocusSize = d_focusSize;

    if(d_focusSize == 0){
      Assert(d_errorSize == d_errorSet.errorSize());
      Assert(d_focusErrorVar == ARITHVAR_SENTINEL);

      d_errorSet.blur();

      d_focusSize = d_errorSet.focusSize();

      Assert( d_errorSize == d_focusSize);
      Assert( d_errorSize >= 1 );

      constructFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);

      Debug("dualLike") << "blur " << d_focusSize << endl;
    }else if(d_focusSize == 1){
      // Possible outcomes:
      // - errorSet size shrunk
      // -- fixed v
      // -- fixed something other than v
      // - conflict
      // - budget was exhausted

      ArithVar e = d_errorSet.topFocusVariable();
      Debug("dualLike") << "primalImproveError " << e << endl;
      dropped = primalImproveError(e);
    }else{

      // Possible outcomes:
      // - errorSet size shrunk
      // -- fixed v
      // -- fixed something other than v
      // - conflict
      // - budget was exhausted
      // - focus went down
      Assert(d_focusSize > 1);
      ArithVar e = d_errorSet.topFocusVariable();
      static const unsigned s_sumMetricThreshold = 1;
      if(d_errorSet.sumMetric(e) <= s_sumMetricThreshold){
        Debug("dualLike") << "dualLikeImproveError " << e << endl;

        dropped = dualLikeImproveError(e);
      }else{
        Debug("dualLike") << "selectFocusImproving " << e << endl;
        int before = d_errorSize;
        selectFocusImproving();
        int after = d_errorSize;
        dropped = before - after;
      }
    }
    Assert(d_focusSize == d_errorSet.focusSize());
    Assert(d_errorSize == d_errorSet.errorSize());

    if(dropped < 0 && d_errorSize/2 >= d_focusSize && d_focusSize >= 1){
      Debug("dualLike") << "dropped " << dropped << endl;
      Debug("dualLike") << "relaxing focus " << endl;

      d_errorSet.clearFocus();
      adjustFocusAndError(false);
    }
    if(verbose){
      if(!d_conflictVariables.empty()){
        cout << "DLV found conflict" << endl;
      }else if(d_pivotBudget == 0){
        cout << "DLV budget exhausted" << endl;
      }else if(dropped < 0){
        cout << "DLV dropped " << dropped << endl;
      }else if(d_focusSize < prevFocusSize){
        // focus went down
        cout << "DLV focus went down" << endl;
      }else{
        cout << "DLV dualLikeImproveError pivot" << endl;
      }
    }
  }


  if(d_focusErrorVar != ARITHVAR_SENTINEL){
    tearDownFocusErrorFunction(d_statistics.d_fcFocusConstructionTimer);
  }

  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
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
