/*********************                                                        */
/*! \file simplex.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): kshitij, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is an implementation of the Simplex Module for the Simplex for DPLL(T)
 ** decision procedure.
 **
 ** This implements the Simplex module for the Simpelx for DPLL(T) decision procedure.
 ** See the Simplex for DPLL(T) technical report for more background.(citation?)
 ** This shares with the theory a Tableau, and a PartialModel that:
 **  - satisfies the equalities in the Tableau, and
 **  - the assignment for the non-basic variables satisfies their bounds.
 ** This is required to either produce a conflict or satisifying PartialModel.
 ** Further, we require being told when a basic variable updates its value.
 **
 ** During the Simplex search we maintain a queue of variables.
 ** The queue is required to contain all of the basic variables that voilate their bounds.
 ** As elimination from the queue is more efficient to be done lazily,
 ** we do not maintain that the queue of variables needs to be only basic variables or only
 ** variables that satisfy their bounds.
 **
 ** The simplex procedure roughly follows Alberto's thesis. (citation?)
 ** There is one round of selecting using a heuristic pivoting rule. (See PreferenceFunction
 ** Documentation for the available options.)
 ** The non-basic variable is the one that appears in the fewest pivots. (Bruno says that
 ** Leonardo invented this first.)
 ** After this, Bland's pivot rule is invoked.
 **
 ** During this proccess, we periodically inspect the queue of variables to
 ** 1) remove now extraneous extries,
 ** 2) detect conflicts that are "waiting" on the queue but may not be detected by the
 **  current queue heuristics, and
 ** 3) detect multiple conflicts.
 **
 ** Conflicts are greedily slackened to use the weakest bounds that still produce the
 ** conflict.
 **
 ** Extra things tracked atm: (Subject to change at Tim's whims)
 ** - A superset of all of the newly pivoted variables.
 ** - A queue of additional conflicts that were discovered by Simplex.
 **   These are theory valid and are currently turned into lemmas
 **/


#include "cvc4_private.h"

#pragma once

#include "theory/arith/arithvar.h"
#include "theory/arith/error_set.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/matrix.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/linear_equality.h"

#include "context/cdlist.h"

#include "util/dense_map.h"
#include "options/options.h"
#include "util/statistics_registry.h"
#include "util/result.h"

#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class SimplexDecisionProcedure {
protected:
  /** The set of variables that are in conflict in this round. */
  DenseSet d_conflictVariables;

  /** The rule to use for heuristic selection mode. */
  ErrorSelectionRule d_heuristicRule;

  /** Linear equality module. */
  LinearEqualityModule& d_linEq;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   * Partial model matches that in LinearEqualityModule.
   */
  ArithVariables& d_variables;

  /**
   * Stores the linear equalities used by Simplex.
   * Tableau from the LinearEquality module.
   */
  Tableau& d_tableau;

  /** Contains a superset of the basic variables in violation of their bounds. */
  ErrorSet& d_errorSet;

  /** Number of variables in the system. This is used for tuning heuristics. */
  ArithVar d_numVariables;

  /** This is the call back channel for Simplex to report conflicts. */
  RaiseConflict d_conflictChannel;

  /** Used for requesting d_opt, bound and error variables for primal.*/
  TempVarMalloc d_arithVarMalloc;

  /** The size of the error set. */
  uint32_t d_errorSize;

  /** The size of the focus set. */
  uint32_t d_focusSize;

  /** The current error focus variable. */
  ArithVar d_focusErrorVar;

  void constructFocusErrorFunction();
  void tearDownFocusErrorFunction();

  void reconstructFocusErrorFunction(){
    tearDownFocusErrorFunction();
    constructFocusErrorFunction();
  }

  /**
   * The signs of the coefficients in the focus set.
   * This is empty until this has been loaded.
   */
  DenseMap<int> d_focusSgns;

  /**
   * Loads the signs of the coefficients of the variables on the row d_focusErrorVar
   * into d_focusSgns.
   */
  void loadFocusSigns();

  /** Unloads the information from d_focusSgns. */
  void unloadFocusSigns();

  /** 
   * The signs of a variable in the row of d_focusErrorVar.
   * d_focusSgns must be loaded.
   */
  int focusSgn(ArithVar nb) const;

public:
  SimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  /**
   * Tries to update the assignments of variables such that all of the
   * assignments are consistent with their bounds.
   * This is done by a simplex search through the possible bases of the tableau.
   *
   * If all of the variables can be made consistent with their bounds
   * SAT is returned. Otherwise UNSAT is returned, and at least 1 conflict
   * was reported on the conflictCallback passed to the Module.
   *
   * Tableau pivoting is performed so variables may switch from being basic to
   * nonbasic and vice versa.
   *
   * Corresponds to the "check()" procedure in [Cav06].
   */
  virtual Result::Sat findModel(bool exactResult) = 0;

  void increaseMax() { d_numVariables++; }

protected:

  /** Reports a conflict to on the output channel. */
  void reportConflict(ArithVar basic);

  /**
   * Checks a basic variable, b, to see if it is in conflict.
   * If a conflict is discovered a node summarizing the conflict is returned.
   * Otherwise, Node::null() is returned.
   */
  Node maybeGenerateConflictForBasic(ArithVar basic) const;

  bool checkBasicForConflict(ArithVar b) const;
  Node generatConflictForBasic(ArithVar basic) const;


  /** Gets a fresh variable from TheoryArith. */
  ArithVar requestVariable(){
    return d_arithVarMalloc.request();
  }

  /** Releases a requested variable from TheoryArith.*/
  void releaseVariable(ArithVar v){
    d_arithVarMalloc.release(v);
  }

  /** Post condition: !d_queue.moreSignals() */
  bool standardProcessSignals(TimerStat &timer, IntStat& conflictStat);

};/* class SimplexDecisionProcedure */

class DualSimplexDecisionProcedure : public SimplexDecisionProcedure{
public:
  DualSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  Result::Sat findModel(bool exactResult) {
    return dualFindModel(exactResult);
  }

private:

  /**
   * Maps a variable to how many times they have been used as a pivot in the
   * simplex search.
   */
  DenseMultiset d_pivotsInRound;

  Result::Sat dualFindModel(bool exactResult);

  /**
   * This is the main simplex for DPLL(T) loop.
   * It runs for at most maxIterations.
   *
   * Returns true iff it has found a conflict.
   * d_conflictVariable will be set and the conflict for this row is reported.
   */
  bool searchForFeasibleSolution(uint32_t maxIterations);
  

  bool processSignals(){
    TimerStat &timer = d_statistics.d_processSignalsTime;
    IntStat& conflictStat  = d_statistics.d_recentViolationCatches;
    return standardProcessSignals(timer, conflictStat);
  }
  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statUpdateConflicts;
    TimerStat d_processSignalsTime;
    IntStat d_simplexConflicts;
    IntStat d_recentViolationCatches;
    TimerStat d_searchTime;

    Statistics();
    ~Statistics();
  } d_statistics;
};/* class DualSimplexDecisionProcedure */


class PureUpdateSimplexDecisionProcedure : public SimplexDecisionProcedure{
public:
  PureUpdateSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  Result::Sat findModel(bool exactResult);

private:
  ArithVar d_focusErrorVar;
  DeltaRational d_focusThreshold;

  bool attemptPureUpdates();

  /**
   * This is the main simplex for DPLL(T) loop.
   * It runs for at most maxIterations.
   *
   * Returns true iff it has found a conflict.
   * d_conflictVariable will be set and the conflict for this row is reported.
   */
  bool searchForFeasibleSolution(uint32_t maxIterations);

  bool processSignals(){
    TimerStat &timer = d_statistics.d_processSignalsTime;
    IntStat& conflictStat  = d_statistics.d_foundConflicts;
    return standardProcessSignals(timer, conflictStat);
  }

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_pureUpdateFoundUnsat;
    IntStat d_pureUpdateFoundSat;
    IntStat d_pureUpdateMissed;
    IntStat d_pureUpdates;
    IntStat d_pureUpdateDropped;
    IntStat d_pureUpdateConflicts;

    IntStat d_foundConflicts;

    TimerStat d_attemptPureUpdatesTimer;
    TimerStat d_processSignalsTime;
    

    Statistics();
    ~Statistics();
  } d_statistics;
};/* class PureUpdateSimplexDecisionProcedure */

class FCSimplexDecisionProcedure : public SimplexDecisionProcedure{
public:
  FCSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  Result::Sat findModel(bool exactResult) { Unreachable(); }

  // other error variables are dropping
  // 
  uint32_t dualLikeImproveError(ArithVar evar);
  uint32_t primalImproveError(ArithVar evar);

  // dual like
  // - found conflict
  // - satisfied error set
  Result::Sat dualLike();

private:

  int32_t d_pivotBudget;
  enum PivotImprovement {
    ErrorDropped,
    NonDegenerate,
    HeuristicDegenerate,
    BlandsDegenerate
  };

  PivotImprovement d_prevPivotImprovement;
  uint32_t d_pivotImprovementInARow;

  uint32_t degeneratePivotsInARow() const {
    switch(d_prevPivotImprovement){
    case ErrorDropped:
    case NonDegenerate:
      return 0;
    case HeuristicDegenerate:
    case BlandsDegenerate:
      return d_pivotImprovementInARow;
    }
    Unreachable();
  }

  static const uint32_t s_focusThreshold = 6;
  static const uint32_t s_maxDegeneratePivotsBeforeBlands = 10;

  ArithVarVec d_sgnDisagreement;

  static PivotImprovement pivotImprovement(const UpdateInfo& selected, bool useBlands = false) {
    if(selected.d_errorsFixed > 0){
      return ErrorDropped;
    }else if(selected.d_degenerate){
      if(useBlands){
        return BlandsDegenerate;
      }else{
        return HeuristicDegenerate;
      }
    }else{
      return NonDegenerate;
    }
  }
  void logPivot(const UpdateInfo& selected, bool useBlands = false){
    if(d_pivotBudget > 0) {
      --d_pivotBudget;
    }
    PivotImprovement curr = pivotImprovement(selected, useBlands);
    if(curr == d_prevPivotImprovement){
      ++d_pivotImprovementInARow;
      if(d_pivotImprovementInARow == 0){
        --d_pivotImprovementInARow;
      }
    }else if(useBlands){
      // keep d_pivotImprovementInARow as the same
      d_prevPivotImprovement = curr;
    }else{
      d_prevPivotImprovement = curr;
      d_pivotImprovementInARow = 1;
    }
  }

  void updateAndSignal(const UpdateInfo& selected);
  UpdateInfo selectPrimalUpdate(ArithVar error, int sgn, LinearEqualityModule::UpdatePreferenceFunction upf, LinearEqualityModule::VarPreferenceFunction bpf, bool storeDisagreements);


  UpdateInfo selectUpdateForDualLike(ArithVar basic, int sgn){
    LinearEqualityModule::UpdatePreferenceFunction upf =
      &LinearEqualityModule::preferErrorsFixed<true>;
    LinearEqualityModule::VarPreferenceFunction bpf =
      &LinearEqualityModule::minRowLength;
    return selectPrimalUpdate(basic, sgn, upf, bpf, true);
  }

  UpdateInfo selectUpdateForPrimal(ArithVar basic, int sgn, bool useBlands){
    LinearEqualityModule::UpdatePreferenceFunction upf = useBlands ?
      &LinearEqualityModule::preferErrorsFixed<false>:
      &LinearEqualityModule::preferErrorsFixed<true>;

    LinearEqualityModule::VarPreferenceFunction bpf = useBlands ?
      &LinearEqualityModule::minVarOrder :
      &LinearEqualityModule::minRowLength;

    return selectPrimalUpdate(basic, sgn, upf, bpf, false);
  }

  void focusUsingSignDisagreements(ArithVar basic, int dir);
  void reajustSizesAfterSignals();

  /**
   * This is the main simplex for DPLL(T) loop.
   * It runs for at most maxIterations.
   *
   * Returns true iff it has found a conflict.
   * d_conflictVariable will be set and the conflict for this row is reported.
   */
  bool searchForFeasibleSolution(uint32_t maxIterations);

  bool processSignals(){
    TimerStat &timer = d_statistics.d_processSignalsTime;
    IntStat& conflictStat  = d_statistics.d_foundConflicts;
    return standardProcessSignals(timer, conflictStat);
  }

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    TimerStat d_processSignalsTime;
    IntStat d_foundConflicts;

    Statistics();
    ~Statistics();
  } d_statistics;
};/* class FCSimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

