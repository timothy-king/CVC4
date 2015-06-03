/*********************                                                        */
/*! \file congruence_manager.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic, Morgan Deters
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

#include "cvc4_private.h"

#pragma once

#include "theory/arith/arithvar.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/callbacks.h"

#include "context/cdo.h"
#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "context/context.h"
#include "context/cdtrail_queue.h"
#include "context/cdmaybe.h"

#include "util/statistics_registry.h"
#include "util/dense_map.h"

// forward declarations
namespace CVC4 {
namespace theory {
class RaiseEqualityEngineConflict;
namespace eq {
class EqualityEngine;
class EqualityEngineNotify;
}/* CVC4::theory::eq namespace */
namespace arith {
class ArithVariables;
class ArithCongruenceNotify;
}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

namespace CVC4 {
namespace theory {
namespace arith {
class ArithCongruenceManager {
private:
  friend class ArithCongruenceNotify;
  
  context::CDRaised d_inConflict;
  RaiseEqualityEngineConflict d_raiseConflict;

  /**
   * The set of ArithVars equivalent to a pair of terms.
   * If this is 0 or cannot be 0, this can be signalled.
   * The pair of terms for the congruence is stored in watched equalities.
   */
  DenseSet d_watchedVariables;
  /** d_watchedVariables |-> (= x y) */
  ArithVarToNodeMap d_watchedEqualities;

  eq::EqualityEngineNotify* d_notify;

  context::CDList<Node> d_keepAlive;

  /** Store the propagations. */
  context::CDTrailQueue<Node> d_propagatations;

  /* This maps the node a theory engine will request on an explain call to
   * to its corresponding PropUnit.
   * This is node is potentially both the propagation or
   * Rewriter::rewrite(propagation).
   */
  typedef context::CDHashMap<Node, size_t, NodeHashFunction> ExplainMap;
  ExplainMap d_explanationMap;

  ConstraintDatabase& d_constraintDatabase;
  SetupLiteralCallBack d_setupLiteral;

  const ArithVariables& d_avariables;

  eq::EqualityEngine* d_ee;

  void raiseConflict(Node conflict);
public:

  bool inConflict() const;

  bool hasMorePropagations() const;

  const Node getNextPropagation();

  bool canExplain(TNode n) const;

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

private:
  Node externalToInternal(TNode n) const;

  void pushBack(TNode n);

  void pushBack(TNode n, TNode r);

  void pushBack(TNode n, TNode r, TNode w);

  bool propagate(TNode x);
  void explain(TNode literal, std::vector<TNode>& assumptions);


  /** This sends a shared term to the uninterpreted equality engine. */
  void assertionToEqualityEngine(bool eq, ArithVar s, TNode reason);

  /** Dequeues the delay queue and asserts these equalities.*/
  void enableSharedTerms();
  void dequeueLiterals();

  void enqueueIntoNB(const std::set<TNode> all, NodeBuilder<>& nb);

  Node explainInternal(TNode internal);

public:

  ArithCongruenceManager(context::Context* satContext, ConstraintDatabase&, SetupLiteralCallBack, const ArithVariables&, RaiseEqualityEngineConflict raiseConflict);

  ~ArithCongruenceManager();
  
  Node explain(TNode literal);
  void explain(TNode lit, NodeBuilder<>& out);

  void addWatchedPair(ArithVar s, TNode x, TNode y);
  void removeWatchedVariable(ArithVar s);

  inline bool isWatchedVariable(ArithVar s) const {
    return d_watchedVariables.isMember(s);
  }

  /** Assert an equality. */
  void watchedVariableIsZero(ConstraintCP eq);

  /** Assert a conjunction from lb and ub. */
  void watchedVariableIsZero(ConstraintCP lb, ConstraintCP ub);

  /** Assert that the value cannot be zero. */
  void watchedVariableCannotBeZero(ConstraintCP c);

  /** Assert that the value cannot be zero. */
  void watchedVariableCannotBeZero(ConstraintCP c, ConstraintCP d);


  /** Assert that the value is congruent to a constant. */
  void equalsConstant(ConstraintCP eq);
  void equalsConstant(ConstraintCP lb, ConstraintCP ub);


  void addSharedTerm(Node x);

private:
  class Statistics {
  public:
    IntStat d_watchedVariables;
    IntStat d_watchedVariableIsZero;
    IntStat d_watchedVariableIsNotZero;

    IntStat d_equalsConstantCalls;

    IntStat d_propagations;
    IntStat d_propagateConstraints;
    IntStat d_conflicts;

    Statistics();
    ~Statistics();
  } d_statistics;

};/* class ArithCongruenceManager */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
