/*********************                                                        */
/*! \file callbacks.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#pragma once

#include "expr/node.h"
#include "util/rational.h"

#include "theory/arith/theory_arith_private_forward.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/bound_counts.h"
#include "theory/arith/constraint_forward.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * ArithVarCallBack provides a mechanism for agreeing on callbacks while
 * breaking mutual recursion inclusion order problems.
 */
class ArithVarCallBack {
public:
  virtual void operator()(ArithVar x) = 0;
};

/**
 * Requests arithmetic variables for internal use,
 * and releases arithmetic variables that are no longer being used.
 */
class ArithVarMalloc {
public:
  virtual ArithVar request() = 0;
  virtual void release(ArithVar v) = 0;
};

class TNodeCallBack {
public:
  virtual void operator()(TNode n) = 0;
};

class NodeCallBack {
public:
  virtual void operator()(Node n) = 0;
};

class RationalCallBack {
public:
  virtual Rational operator()() const = 0;
};

class SetupLiteralCallBack : public TNodeCallBack {
private:
  TheoryArithPrivate& d_arith;
public:
  SetupLiteralCallBack(TheoryArithPrivate& ta);
  void operator()(TNode lit);
};

class DeltaComputeCallback : public RationalCallBack {
private:
  const TheoryArithPrivate& d_ta;
public:
  DeltaComputeCallback(const TheoryArithPrivate& ta);
  Rational operator()() const;
};

class BasicVarModelUpdateCallBack : public ArithVarCallBack{
private:
  TheoryArithPrivate& d_ta;
public:
  BasicVarModelUpdateCallBack(TheoryArithPrivate& ta);
  void operator()(ArithVar x);
};

class TempVarMalloc : public ArithVarMalloc {
private:
  TheoryArithPrivate& d_ta;
public:
  TempVarMalloc(TheoryArithPrivate& ta);
  ArithVar request();
  void release(ArithVar v);
};

class _RaiseConflict {
private:
  TheoryArithPrivate& d_ta;
public:
  _RaiseConflict(TheoryArithPrivate& ta);

  /** Calls d_ta.raiseConflict(c) */
  void raiseConflict(ConstraintCP c) const;
};

class FarkasConflictBuilder {
private:
  RationalVector d_farkas;
  ConstraintCPVec d_constraints;
  ConstraintCP d_consequent;
  bool d_consequentSet;
  
public:

  /**
   * Constructs a new FarkasConflictBuilder.
   */
  FarkasConflictBuilder();

  /**
   * Adds an antecedent constraint to the conflict under construction
   * with the farkas coefficient fc.
   */
  void addConstraint(ConstraintCP c, const Rational& fc);

  /**
   * Makes the last constraint added the consequent.
   * Can be done exactly once per reset().
   */
  void makeLastConsequent();
  
  /**
   * Turns the antecendents into a proof of the negation of one of the
   * antecedents.
   *
   * The buffer is no longer underConstruction afterwards.
   *
   * precondition:
   * - At least two constraints have been asserted.
   * - makeLastConsequent() has been called.
   *
   * postcondition: The returned constraint is in conflict.
   */
  ConstraintCP commitConflict();

  /** Returns true if a conflict has been pushed back since the last reset. */
  bool underConstruction() const;

  
  /** Resets the state of the buffer. */
  void reset();
};


class RaiseEqualityEngineConflict {
private:
  TheoryArithPrivate& d_ta;
  
public:
  RaiseEqualityEngineConflict(TheoryArithPrivate& ta);

  /* If you are not an equality engine, don't use this! */
  void raiseEEConflict(Node n) const;
};

class BoundCountingLookup {
private:
  TheoryArithPrivate& d_ta;
public:
  BoundCountingLookup(TheoryArithPrivate& ta);
  const BoundsInfo& boundsInfo(ArithVar basic) const;
  BoundCounts atBounds(ArithVar basic) const;
  BoundCounts hasBounds(ArithVar basic) const;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
