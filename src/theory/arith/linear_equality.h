/*********************                                                        */
/*! \file linear_equality.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This module maintains the relationship between a Tableau and PartialModel.
 **
 ** This shares with the theory a Tableau, and a PartialModel that:
 **  - satisfies the equalities in the Tableau, and
 **  - the assignment for the non-basic variables satisfies their bounds.
 ** This maintains the relationship needed by the SimplexDecisionProcedure.
 **
 ** In the language of Simplex for DPLL(T), this provides:
 ** - update()
 ** - pivotAndUpdate()
 **
 ** This class also provides utility functions that require
 ** using both the Tableau and PartialModel.
 **/


#include "cvc4_private.h"

#pragma once

#include "theory/arith/delta_rational.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/matrix.h"
#include "theory/arith/constraint.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {


class LinearEqualityModule {
public:
  typedef ArithVar (LinearEqualityModule::*PreferenceFunction)(ArithVar, ArithVar) const;

private:  
  /**
   * Manages information about the assignment and upper and lower bounds on the
   * variables.
   */
  ArithVariables& d_variables;

  /** Reference to the Tableau to operate upon. */
  Tableau& d_tableau;

  /** Called whenever the value of a basic variable is updated. */
  ArithVarCallBack& d_basicVariableUpdates;

public:

  /**
   * Initializes a LinearEqualityModule with a partial model, a tableau,
   * and a callback function for when basic variables update their values.
   */
  LinearEqualityModule(ArithVariables& vars, Tableau& t, ArithVarCallBack& f);

  /**
   * Updates the assignment of a nonbasic variable x_i to v.
   * Also updates the assignment of basic variables accordingly.
   */
  void update(ArithVar x_i, const DeltaRational& v);

  /**
   * Updates the value of a basic variable x_i to v,
   * and then pivots x_i with the nonbasic variable in its row x_j.
   * Updates the assignment of the other basic variables accordingly.
   */
  void pivotAndUpdate(ArithVar x_i, ArithVar x_j, const DeltaRational& v);


  ArithVariables& getVariables() const{ return d_variables; }
  Tableau& getTableau() const{ return d_tableau; }


  bool hasBounds(ArithVar basic, bool upperBound);
  bool hasLowerBounds(ArithVar basic){
    return hasBounds(basic, false);
  }
  bool hasUpperBounds(ArithVar basic){
    return hasBounds(basic, true);
  }


  void startTrackingBoundCounts();
  void stopTrackingBoundCounts();

private:

  // RowIndex -> BoundCount
  typedef DenseMap<BoundCounts> BoundCountingVector;
  BoundCountingVector d_boundTracking;
  bool d_areTracking;

  /**
   * Exports either the explanation of an upperbound or a lower bound
   * of the basic variable basic, using the non-basic variables in the row.
   */
  template <bool upperBound>
  void propagateNonbasics(ArithVar basic, Constraint c);

public:
  void propagateNonbasicsLowerBound(ArithVar basic, Constraint c){
    Assert(c->isLowerBound());
    propagateNonbasics<false>(basic, c);
  }
  void propagateNonbasicsUpperBound(ArithVar basic, Constraint c){
    Assert(c->isUpperBound());
    propagateNonbasics<true>(basic, c);
  }

  /**
   * Computes the value of a basic variable using the assignments
   * of the values of the variables in the basic variable's row tableau.
   * This can compute the value using either:
   * - the the current assignment (useSafe=false) or
   * - the safe assignment (useSafe = true).
   */
  DeltaRational computeRowValue(ArithVar x, bool useSafe);

  inline DeltaRational computeLowerBound(ArithVar basic){
    return computeBound(basic, false);
  }
  inline DeltaRational computeUpperBound(ArithVar basic){
    return computeBound(basic, true);
  }

  /**
   * A PreferenceFunction takes a const ref to the SimplexDecisionProcedure,
   * and 2 ArithVar variables and returns one of the ArithVar variables
   * potentially using the internals of the SimplexDecisionProcedure.
   */

  ArithVar noPreference(ArithVar x, ArithVar y) const{
    return x;
  }

  /**
   * minVarOrder is a PreferenceFunction for selecting the smaller of the 2
   * ArithVars. This PreferenceFunction is used during the VarOrder stage of
   * findModel.
   */
  ArithVar minVarOrder(ArithVar x, ArithVar y) const;

  /**
   * minColLength is a PreferenceFunction for selecting the variable with the
   * smaller row count in the tableau.
   *
   * This is a heuristic rule and should not be used during the VarOrder
   * stage of findModel.
   */
  ArithVar minColLength(ArithVar x, ArithVar y) const;

  /**
   * minRowLength is a PreferenceFunction for selecting the variable with the
   * smaller row count in the tableau.
   *
   * This is a heuristic rule and should not be used during the VarOrder
   * stage of findModel.
   */
  ArithVar minRowLength(ArithVar x, ArithVar y) const;

  /**
   * minBoundAndRowCount is a PreferenceFunction for preferring a variable
   * without an asserted bound over variables with an asserted bound.
   * If both have bounds or both do not have bounds,
   * the rule falls back to minRowCount(...).
   *
   * This is a heuristic rule and should not be used during the VarOrder
   * stage of findModel.
   */
  ArithVar minBoundAndColLength(ArithVar x, ArithVar y) const;


  template <bool above>
  inline bool isAcceptableSlack(int sgn, ArithVar nonbasic) const {
    return
      ( above && sgn < 0 && d_variables.strictlyBelowUpperBound(nonbasic)) ||
      ( above && sgn > 0 && d_variables.strictlyAboveLowerBound(nonbasic)) ||
      (!above && sgn > 0 && d_variables.strictlyBelowUpperBound(nonbasic)) ||
      (!above && sgn < 0 && d_variables.strictlyAboveLowerBound(nonbasic));
  }

  /**
   * Given the basic variable x_i,
   * this function finds the smallest nonbasic variable x_j in the row of x_i
   * in the tableau that can "take up the slack" to let x_i satisfy its bounds.
   * This returns ARITHVAR_SENTINEL if none exists.
   *
   * More formally one of the following conditions must be satisfied:
   * -  lowerBound && a_ij < 0 && assignment(x_j) < upperbound(x_j)
   * -  lowerBound && a_ij > 0 && assignment(x_j) > lowerbound(x_j)
   * - !lowerBound && a_ij > 0 && assignment(x_j) < upperbound(x_j)
   * - !lowerBound && a_ij < 0 && assignment(x_j) > lowerbound(x_j)
   *
   */
  template <bool lowerBound>  ArithVar selectSlack(ArithVar x_i, PreferenceFunction pf) const;
  ArithVar selectSlackLowerBound(ArithVar x_i, PreferenceFunction pf) const {
    return selectSlack<true>(x_i, pf);
  }
  ArithVar selectSlackUpperBound(ArithVar x_i, PreferenceFunction pf) const {
    return selectSlack<false>(x_i, pf);
  }

  inline bool basicIsTracked(ArithVar v) const {
    return d_boundTracking.isKey(v);
  }

  BoundCounts computeBoundCounts(ArithVar x_i) const;
  BoundCounts cachingCountBounds(ArithVar x_i) const;
  BoundCounts countBounds(ArithVar x_i);
  void trackingCoefficientChange(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn);

  void trackingSwap(ArithVar basic, ArithVar nb, int sgn);


  bool nonbasicsAtLowerBounds(ArithVar x_i) const;
  bool nonbasicsAtUpperBounds(ArithVar x_i) const;

  ArithVar _anySlackLowerBound(ArithVar x_i) const {
    return selectSlack<true>(x_i, &LinearEqualityModule::noPreference);
  }
  ArithVar _anySlackUpperBound(ArithVar x_i) const {
    return selectSlack<false>(x_i, &LinearEqualityModule::noPreference);
  }

private:
  class TrackingCallback : public CoefficientChangeCallback {
  private:
    LinearEqualityModule* d_linEq;
  public:
    TrackingCallback(LinearEqualityModule* le) : d_linEq(le) {}
    void update(ArithVar basic, ArithVar nb, int oldSgn, int currSgn){
      d_linEq->trackingCoefficientChange(basic, nb, oldSgn, currSgn);
    }
    void swap(ArithVar basic, ArithVar nb, int oldNbSgn){
      d_linEq->trackingSwap(basic, nb, oldNbSgn);
    }

 } d_trackCallback;

  /**
   * Selects the constraint for the variable v on the row for basic
   * with the weakest possible constraint that is consistent with the surplus
   * surplus.
   */
  Constraint weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v,
                                const Rational& coeff, bool& anyWeakening, ArithVar basic) const;

public:
  /**
   * Constructs a minimally weak conflict for the basic variable basicVar.
   */
  Node minimallyWeakConflict(bool aboveUpper, ArithVar basicVar) const;

  /**
   * Given a non-basic variable that is know to have a conflict on it,
   * construct and return a conflict.
   * Follows section 4.2 in the CAV06 paper.
   */
  inline Node generateConflictAboveUpperBound(ArithVar conflictVar) const {
    return minimallyWeakConflict(true, conflictVar);
  }

  inline Node generateConflictBelowLowerBound(ArithVar conflictVar) const {
    return minimallyWeakConflict(false, conflictVar);
  }

private:
  DeltaRational computeBound(ArithVar basic, bool upperBound);

public:
  /**
   * Checks to make sure the assignment is consistent with the tableau.
   * This code is for debugging.
   */
  void debugCheckTableau();

  void debugCheckTracking();

  /** Debugging information for a pivot. */
  void debugPivot(ArithVar x_i, ArithVar x_j);

  /** Checks the tableau + partial model for consistency. */
  bool debugEntireLinEqIsConsistent(const std::string& s);


private:
  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statPivots, d_statUpdates;
    TimerStat d_pivotTime;

    IntStat d_weakeningAttempts, d_weakeningSuccesses, d_weakenings;
    TimerStat d_weakenTime;

    Statistics();
    ~Statistics();
  };
  mutable Statistics d_statistics;

};/* class LinearEqualityModule */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
