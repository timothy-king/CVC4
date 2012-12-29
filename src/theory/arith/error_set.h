/*********************                                                        */
/*! \file arith_priority_queue.h
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


#include "cvc4_private.h"

#pragma once

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/arith_heuristic_pivot_rule.h"

#include "util/statistics_registry.h"
#include <boost/heap/d_ary_heap.hpp>


#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {


/**
 * The priority queue has 3 different modes of operation:
 * - Collection
 *   This passively collects arithmetic variables that may be inconsistent.
 *   This does not maintain any heap structure.
 *   dequeueInconsistentBasicVariable() does not work in this mode!
 *   Entering this mode requires the queue to be empty.
 *
 * - Difference Queue
 *   This mode uses the difference between a variables and its bound
 *   to determine which to dequeue first.
 *
 * - Variable Order Queue
 *   This mode uses the variable order to determine which ArithVar is dequeued first.
 *
 * The transitions between the modes of operation are:
 *  Collection => Difference Queue
 *  Difference Queue => Variable Order Queue
 *  Difference Queue => Collection (queue must be empty!)
 *  Variable Order Queue => Collection (queue must be empty!)
 *
 * The queue begins in Collection mode.
 */



class ErrorInfoMap;

class ComparatorPivotRule {
private:
  const ErrorInfoMap* d_errInfo;
  ErrorSelectionRule d_rule;
 
public:
  ComparatorPivotRule();
  ComparatorPivotRule(const ErrorInfoMap* es, ErrorSelectionRule r);

  bool operator()(ArithVar v, ArithVar u) const;
  ErrorSelectionRule getRule() const { return d_rule; }
};

typedef boost::heap::d_ary_heap<
  ArithVar,
  boost::heap::arity<2>,
  boost::heap::compare<ComparatorPivotRule>,
  boost::heap::mutable_<true> > ErrorSetHeap;

typedef ErrorSetHeap::handle_type ErrorSetHandle;

class ErrorInformation {
private:
  /** The variable that is in error. */
  ArithVar d_variable;

  /**
   * The constraint that was violated.
   * This needs to be saved in case that the 
   * violated constraint  
   */
  Constraint d_violated;

  /**
   * This is the sgn of the first derivate the variable must move to satisfy
   * the bound violated.
   * If d_sgn > 0, then d_violated was a lowerbound.
   * If d_sgn < 0, then d_violated was an upperbound.
   */
  int d_sgn;

  /**
   * If this is true, then the bound is no longer set on d_variables.
   * This MUST be undone before this is deleted.
   */
  bool d_relaxed;

  /**
   * If this is true, then the variable is in the focus set and the focus heap.
   * d_handle is then a reasonable thing to interpret.
   * If this is false, the variable is somewhere in 
   */
  bool d_inFocus;
  ErrorSetHandle d_handle;

  DeltaRational* d_amount;

public:
  ErrorInformation();
  ErrorInformation(ArithVar var, Constraint vio, int sgn);
  ~ErrorInformation();
  ErrorInformation(const ErrorInformation& ei);
  ErrorInformation& operator=(const ErrorInformation& ei);

  void reset(Constraint c, int sgn);

  inline ArithVar getVariable() const { return d_variable; }

  bool isRelaxed() const { return d_relaxed; }
  void setRelaxed(){ Assert(!d_relaxed); d_relaxed = true; }
  void setUnrelaxed(){ Assert(d_relaxed); d_relaxed = false; }

  inline int sgn() const { return d_sgn; }
 
  inline bool inFocus() const { return d_inFocus; }
  inline void setInFocus(bool inFocus) { d_inFocus = inFocus; }

  const DeltaRational& getAmount() const {
    Assert(d_amount != NULL);
    return *d_amount;
  }

  void setAmount(const DeltaRational& am);

  inline void setHandle(ErrorSetHandle h) {
    Assert(d_inFocus);
    d_handle = h;
  }
  inline const ErrorSetHandle& getHandle() const{ return d_handle; }

  inline Constraint getViolated() const { return d_violated; }

  bool debugInitialized() const {
    return
      d_variable != ARITHVAR_SENTINEL &&
      d_violated != NullConstraint &&
      d_sgn != 0;
  }
};

class ErrorInfoMap : public DenseMap<ErrorInformation> {};

class ErrorSet {
private:
  /**
   * Reference to the arithmetic partial model for checking if a variable
   * is consistent with its upper and lower bounds.
   */
  ArithVariables& d_variables;

  /**
   * The set of all variables that violate exactly one of their bounds.
   */
  ErrorInfoMap d_errInfo;

  /**
   * The ordered heap for the variables that are in ErrorSet.
   */
  ErrorSetHeap d_focus;

  /**
   * A strict subset of the error set.
   *   d_outOfFocus \neq d_errInfo.
   *
   * Its symbolic complement is Focus.
   *   d_outOfFocus \intersect Focus == \emptyset
   *   d_outOfFocus \union Focus == d_errInfo
   */
  ArithVarVec d_outOfFocus;

  /**
   * Before a variable is added to the error set, it is added to the signals list.
   * A variable may appear on the list multiple times.
   * This introduces a delay.
   */
  ArithVarVec d_signals;


  /** A buffer that is now consistent. */
  ArithVarVec d_nowConsistent;


  /**
   * Computes the difference between the assignment and its bound for x.
   */
  DeltaRational computeDiff(ArithVar x) const;
  void recomputeAmount(ErrorInformation& ei, ErrorSelectionRule r);

  void update(ErrorInformation& ei);
  void transitionVariableOutOfError(ArithVar v);
  void transitionVariableIntoError(ArithVar v);
  void dropFromFocus(ArithVar v);
  void addBackIntoFocus(ArithVar v);
  void blur();


public:

  ErrorSet(ArithVariables& var);

  typedef ErrorInfoMap::const_iterator error_iterator;
  error_iterator errorBegin() const { return d_errInfo.begin(); }
  error_iterator errorEnd() const { return d_errInfo.end(); }

  bool inError(ArithVar v) const { return d_errInfo.isKey(v); }

  ErrorSelectionRule getSelectionRule() const;
  void setSelectionRule(ErrorSelectionRule rule);

  inline ArithVar topFocusVariable() const{
    Assert(!focusEmpty());
    return d_focus.top();
  }

  inline void signalVariable(ArithVar var){
    d_signals.push_back(var);
  }

  inline void signalUnderCnd(ArithVar var, bool b){
    if(b){ signalVariable(var); }
  }

  inline bool inconsistent(ArithVar var) const{
    return !d_variables.assignmentIsConsistent(var) ;
  }
  inline void signalIfInconsistent(ArithVar var){
    signalUnderCnd(var, inconsistent(var));
  }

  inline bool errorEmpty() const{
    return d_errInfo.empty();
  }

  inline bool focusEmpty() const {
    return d_focus.empty();
  }

  /** Clears the set. */
  void clear();
  void reduceToSignals();

  bool noSignals() const {
    return d_signals.empty();
  }
  bool moreSignals() const {
    return !noSignals();
  }
  ArithVar topSignal() const {
    Assert(moreSignals());
    return d_signals.back();
  }
  /**
   * Moves a variable out of the signals.
   * This moves it into the error set.
   * 
   */
  void popSignal();

  void popAllSignals(){
    while(moreSignals()){
      popSignal();
    }
  }

private:
  class Statistics {
  public:
    IntStat d_enqueues;
    IntStat d_enqueuesCollection;
    IntStat d_enqueuesDiffMode;
    IntStat d_enqueuesVarOrderMode;

    IntStat d_enqueuesCollectionDuplicates;
    IntStat d_enqueuesVarOrderModeDuplicates;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
