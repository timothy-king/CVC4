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
private:
  /** The set of variables that are in conflict in this round. */
  DenseSet d_conflictVariables;

  /** */
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

  /** Maps a variable to how many times they have been used as a pivot in the simplex search. */
  DenseMultiset d_pivotsInRound;

  /** Stores to the DeltaRational constant 0. */
  DeltaRational d_DELTA_ZERO;

  /** Used for requesting d_opt, bound and error variables for primal.*/
  TempVarMalloc d_arithVarMalloc;

public:
  SimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  /**
   * This must be called when the value of a basic variable may have transitioned
   * from voilating one of its bounds.
   */
  //inline void signal(ArithVar x) { d_queue.signalVariable(x); }

  /** Post condition: !d_queue.moreSignals() */
  bool processSignals();

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
  Result::Sat dualFindModel(bool exactResult);

  void increaseMax() { d_numVariables++; }

private:
  
  /**
   * This is the main simplex for DPLL(T) loop.
   * It runs for at most maxIterations.
   *
   * Returns true iff it has found a conflict.
   * d_conflictVariable will be set and the conflict for this row is reported.
   */
  bool searchForFeasibleSolution(uint32_t maxIterations);

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

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statUpdateConflicts;
    TimerStat d_processSignalsTime;
    IntStat d_simplexConflicts;
    IntStat d_recentViolationCatches;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class SimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

