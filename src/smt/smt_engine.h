/*********************                                           -*- C++ -*-  */
/** smt_engine.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__SMT_ENGINE_H
#define __CVC4__SMT_ENGINE_H

#include <vector>

#include "cvc4_config.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "util/result.h"
#include "util/model.h"
#include "util/options.h"
#include "prop/prop_engine.h"
#include "util/decision_engine.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {

class Command;

// TODO: SAT layer (esp. CNF- versus non-clausal solvers under the
// hood): use a type parameter and have check() delegate, or subclass
// SmtEngine and override check()?
//
// Probably better than that is to have a configuration object that
// indicates which passes are desired.  The configuration occurs
// elsewhere (and can even occur at runtime).  A simple "pass manager"
// of sorts determines check()'s behavior.
//
// The CNF conversion can go on in PropEngine.

class SmtEngine {
  /** Current set of assertions. */
  // TODO: make context-aware to handle user-level push/pop.
  std::vector<Expr> d_assertions;

  /** Our expression manager */
  ExprManager *d_em;

  /** User-level options */
  Options *d_opts;

  /** Expression built-up for handing off to the propagation engine */
  Expr d_expr;

  /** The decision engine */
  DecisionEngine d_de;

  /** The decision engine */
  TheoryEngine d_te;

  /** The propositional engine */
  PropEngine d_prop;

  /**
   * Pre-process an Expr.  This is expected to be highly-variable,
   * with a lot of "source-level configurability" to add multiple
   * passes over the Expr.  TODO: may need to specify a LEVEL of
   * preprocessing (certain contexts need more/less ?).
   */
  Expr preprocess(Expr);

  /**
   * Adds a formula to the current context.
   */
  void addFormula(Expr);

  /**
   * Full check of consistency in current context.  Returns true iff
   * consistent.
   */
  Result check();

  /**
   * Quick check of consistency in current context: calls
   * processAssertionList() then look for inconsistency (based only on
   * that).
   */
  Result quickCheck();

  /**
   * Process the assertion list: for literals and conjunctions of
   * literals, assert to T-solver.
   */
  void processAssertionList();

public:
  /*
   * Construct an SmtEngine with the given expression manager and user options.
   */
  SmtEngine(ExprManager* em, Options* opts) throw() :
    d_em(em),
    d_opts(opts),
    d_expr(Expr::null()),
    d_de(),
    d_te(),
    d_prop(d_de, d_te) {
  }

  /**
   * Execute a command.
   */
  void doCommand(Command*);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false iff
   * inconsistent.
   */
  Result assertFormula(Expr);

  /**
   * Add a formula to the current context and call check().  Returns
   * true iff consistent.
   */
  Result query(Expr);

  /**
   * Add a formula to the current context and call check().  Returns
   * true iff consistent.
   */
  Result checkSat(Expr);

  /**
   * Simplify a formula without doing "much" work.  Requires assist
   * from the SAT Engine.
   */
  Expr simplify(Expr);

  /**
   * Get a (counter)model (only if preceded by a SAT or INVALID query.
   */
  Model getModel();

  /**
   * Push a user-level context.
   */
  void push();

  /**
   * Pop a user-level context.  Throws an exception if nothing to pop.
   */
  void pop();
};/* class SmtEngine */

}/* CVC4 namespace */

#endif /* __CVC4__SMT_ENGINE_H */
