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
 ** \brief This provides a class for summarizing pivot proposals.
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
#include "theory/arith/constraint_forward.h"
#include "util/maybe.h"

namespace CVC4 {
namespace theory {
namespace arith {

enum WitnessImprovement {
  ConflictFound = 0,
  ErrorDropped = 1,
  FocusImproved = 2,
  BlandsDegenerate = 3,
  HeuristicDegenerate = 4,
  AntiProductive = 5
};

inline bool improvement(WitnessImprovement w){
  return w <= FocusImproved;
}

/**
 * This class summarizes both potential:
 * - pivot-and-update operations or
 * - a pure update operation.
 * This stores enough information for the various algorithms  hat consider these operations.
 * These require slightly different pieces of information at different points
 * so they are a bit verbose and paranoid.
 */
class UpdateInfo {
private:

  /**
   * The nonbasic variables under consideration.
   * This is either the entering variable on a pivot and update
   * or the variable being updated.
   * This can only be set in the constructor or assignment.
   *
   * If this uninitialized, then this is ARITHVAR_SENTINEL.
   */
  ArithVar d_nonbasic;

  /**
   * The sgn of the "intended" derivative (delta) of the update to d_nonbasic.
   * This is either 1, -1, or 0.
   * It is "intended" as the delta is always allowed to be 0.
   * (See debugSgnAgreement().)
   *
   * If this uninitialized, then this is 0.
   * If this is initialized, then it is -1 or 1.
   *
   * This can only be set in the constructor or assignment.
   */
  int d_nonbasicDirection;

  /**
   * The change in the assignment of d_nonbasic.
   * This is changed via the updateProposal(...) methods.
   * The value needs to satisfy debugSgnAgreement() or it is in conflict.
   */
  Maybe<DeltaRational> d_nonbasicDelta;

  /**
   * This is true if the pivot-and-update is *known* to cause a conflict.
   * This can only be true if it was constructed through the static conflict(...) method.
   */
  bool d_foundConflict;

  /** This is the change in the size of the error set. */
  Maybe<int> d_errorsChange;

  /** This is the sgn of the change in the value of the focus set.*/
  Maybe<int> d_focusDirection;

  /**
   * This is the constraint that nonbasic is basic is updating s.t. its variable is against it.
   * This has 3 different possibilities:
   * - Unbounded : then this is NullConstraint and unbounded() is true.
   * - Pivot-And-Update: then this is not NullConstraint and the variable is not d_nonbasic.
   * - Update: then this is not NullConstraint and the variable is d_nonbasic.
   */
  Constraint d_limiting;

  /**
   * This returns true if
   * d_nonbasicDelta is zero() or its sgn() must agree with d_nonbasicDirection.
   */
  bool debugSgnAgreement() const {
    int deltaSgn = d_nonbasicDelta.constValue().sgn();
    return deltaSgn == 0 || deltaSgn == d_nonbasicDirection;
  }

  /** This private constructor allows for setting conflict to true. */
  UpdateInfo(bool conflict, ArithVar nb, const DeltaRational& delta, Constraint lim);

public:

  /** This constructs an uninitialized UpdateInfo. */
  UpdateInfo();

  /**
   * This constructs an initialized UpdateInfo.
   * dir must be 1 or -1.
   */
  UpdateInfo(ArithVar nb, int dir);

  /**
   * This updates the nonBasicDelta to d and limiting to NullConstraint.
   * This describes an unbounded() update.
   */
  void updateProposal(const DeltaRational& d);

  /**
   * This updates the nonBasicDelta to d and limiting to c.
   * This clears errorChange() and focusDir().
   */
  void updateProposal(const DeltaRational& d, Constraint c);

  /**
   * This updates the nonBasicDelta to d, limiting to c, and errorChange to e.
   * This clears focusDir().
   */
  void updateProposal(const DeltaRational& d, Constraint c, int e);

  /**
   * This updates the nonBasicDelta to d, limiting to c, errorChange to e and
   * focusDir to f.
   */
  void updateProposal(const DeltaRational& d, Constraint c, int e, int f);


  static UpdateInfo conflict(ArithVar nb, const DeltaRational& delta, Constraint lim);

  inline ArithVar nonbasic() const { return d_nonbasic; }
  inline bool uninitialized() const {
    return d_nonbasic == ARITHVAR_SENTINEL;
  }

  /**
   * There is no limiting value to the improvement of the focus.
   * If this is true, this never describes an update.
   */
  inline bool unbounded() const {
    return d_limiting == NullConstraint;
  }

  /**
   * The update either describes a pivotAndUpdate operation
   * or it describes just an update.
   */
  bool describesPivot() const;

  /** Returns the . describesPivot() must be true. */
  ArithVar leaving() const;

  /**
   * Returns true if this is *known* to find a conflict.
   * If true, this must have been made through the static conflict(...) function.
   */
  bool foundConflict() const { return d_foundConflict; }

  /** Returns the direction nonbasic is supposed to move. */
  inline int nonbasicDirection() const{  return d_nonbasicDirection; }

  /** Requires errorsChange to be set through setErrorsChange or updateProposal. */
  inline int errorsChange() const { return d_errorsChange; }

  /**
   * If errorsChange has been set, return errorsChange().
   * Otherwise, return def.
   */
  inline int errorsChangeSafe(int def) const {
    if(d_errorsChange.just()){
      return d_errorsChange;
    }else{
      return def;
    }
  }

  /** Sets the errorChange. */
  void setErrorsChange(int ec){
    d_errorsChange = ec;
  }


  /** Requires errorsChange to be set through setErrorsChange or updateProposal. */
  inline int focusDirection() const{ return d_focusDirection; }

  /** Sets the focusDirection. */
  void setFocusDirection(int fd){
    Assert(-1 <= fd  && fd <= 1);
    d_focusDirection = fd;
  }

  /**
   * nonbasicDirection must be the same as the sign for the focus function's
   * coefficient for this to be safe.
   * The burden for this being safe is on the user!
   */
  void determineFocusDirection(){
    d_focusDirection =
      (d_nonbasicDirection) * d_nonbasicDelta.constValue().sgn();
  }

  /** Requires nonbasicDelta to be set through updateProposal(...). */
  const DeltaRational& nonbasicDelta() const {
    return d_nonbasicDelta;
  }

  /** Returns the limiting constraint. */
  inline Constraint limiting() const {
    return d_limiting;
  }

  /**
   * Determines the appropraite WitnessImprovement for the update.
   * useBlands breaks ties for degenerate pivots.
   *
   * This is safe if:
   * - d_foundConflict is true, or
   * - d_foundConflict is false and d_errorsChange has been set and d_errorsChange < 0, or
   * - d_foundConflict is false and d_errorsChange has been set and d_errorsChange >= 0 and d_focusDirection has been set.
   */
  WitnessImprovement getWitness(bool useBlands = false) const{
    if(d_foundConflict){
      return ConflictFound;
    }else if(d_errorsChange < 0){
      return ErrorDropped;
    }else if(d_errorsChange == 0){
      if(d_focusDirection > 0){
        return FocusImproved;
      }else if(d_focusDirection == 0){
        if(useBlands){
          return BlandsDegenerate;
        }else{
          return HeuristicDegenerate;
        }
      }
    }
    return AntiProductive;
  }

  /** Outputs the UpdateInfo into out. */
  void output(std::ostream& out) const;
};

std::ostream& operator<<(std::ostream& out, const UpdateInfo& up);

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
