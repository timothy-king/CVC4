
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

class RaiseConflict {
private:
  TheoryArithPrivate& d_ta;
  ConstraintCPVec& d_construction;
public:
  RaiseConflict(TheoryArithPrivate& ta, ConstraintCPVec& d_construction);

  /* Adds a constraint to the constraint under construction. */
  void addConstraint(ConstraintCP c);
  /* Turns the vector under construction into a conflict */
  void commitConflict();

  void sendConflict(const ConstraintCPVec& vec);

  /* If you are not an equality engine, don't use this! */
  void blackBoxConflict(Node n);
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
