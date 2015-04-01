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
  void raiseConflict(ConstraintCP c);
};

class FarkasConflictBuilder {
private:
  _RaiseConflict d_raiseConflict;
  bool d_finalCoeffSet;
  RationalVector d_farkas;
  ConstraintCPVec d_constraints;
  
public:

  /**
   * Constructs a new FarkasConflictBuilder.
   */
  FarkasConflictBuilder(_RaiseConflict& rc);

  /**
   * Adds a constraint to the conflict under construction
   * with the farkas coefficient fc.
   */
  void addConstraint(ConstraintCP c, const Rational& fc);

  /**
   * Turns the vector under construction into a proof for the 
   * negation of c.
   *
   * The farkas coefficient for c is fc.
   *
   * The buffer is no longer underConstruction afterwards.
   */
  void commitConflict(ConstraintCP c, const Rational& fc);

  void setFinalCoefficient( const Rational& fc );
  
  void commitConflict(ConstraintCP c);

  /** Returns true if a conflict has been pushed back since the last reset. */
  bool underConstruction() const;
  
private:
  /** Resets the state of the buffer. */
  void reset();
};


class RaiseEqualityEngineConflict {
private:
  TheoryArithPrivate& d_ta;
  
public:
  RaiseEqualityEngineConflict(TheoryArithPrivate& ta);

  /* If you are not an equality engine, don't use this! */
  void raiseEEConflict(Node n);
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
