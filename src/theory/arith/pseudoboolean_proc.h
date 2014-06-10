#include "cvc4_private.h"

#pragma once

#include <vector>
#include "util/rational.h"
#include "util/maybe.h"
#include "expr/node.h"

#include "context/context.h"
#include "context/cdo.h"
#include "context/cdhashmap.h"

#include "theory/substitutions.h"
#include <ext/hash_set>

namespace CVC4 {
namespace theory {
namespace arith {

class PseudoBooleanProcessor {
private:
  // x ->  <geqZero, leqOne>
  typedef std::pair<Node, Node> PairNode;
  typedef std::vector<Node> NodeVec;
  typedef context::CDHashMap<Node, PairNode, NodeHashFunction> CDNode2PairMap;
  CDNode2PairMap d_pbBounds;
  SubstitutionMap d_subCache;

  typedef __gnu_cxx::hash_set<Node, NodeHashFunction> NodeSet;
  NodeSet d_learningCache;

  context::CDO<unsigned> d_pbs;

  // decompose into \sum pos >= neg + off
  Maybe<Rational> d_off;
  NodeVec d_pos;
  NodeVec d_neg;
  void clear();
  /** Returns true if successful. */
  bool decomposeAssertion(Node assertion, bool negated);

public:
  PseudoBooleanProcessor(context::Context* user_context);

  /** Assumes that the assertions have been rewritten. */
  void learn(const NodeVec& assertions);

  /** Assumes that the assertions have been rewritten. */
  void applyReplacements(NodeVec& assertions);

  bool likelyToHelp() const;

  bool isPseudoBoolean(Node v) const;

  // Adds the fact the that integert typed variable v
  //   must be >= 0 to the context.
  // This is explained by the explanation exp.
  // exp cannot be null.
  void addGeqZero(Node v, Node exp);


  // Adds the fact the that integert typed variable v
  //   must be <= 1 to the context.
  // This is explained by the explanation exp.
  // exp cannot be null.
  void addLeqOne(Node v, Node exp);

  static inline bool isIntVar(Node v){
    return v.isVar() && v.getType().isInteger();
  }

private:
  /** Assumes that the assertion has been rewritten. */
  void learn(Node assertion);

  /** Rewrites a node  */
  Node applyReplacements(Node assertion);

  void learnInternal(Node assertion, bool negated, Node orig);
  void learnRewrittenGeq(Node assertion, bool negated, Node orig);

  void addSub(Node from, Node to);
  void learnGeqSub(Node geq);

  static Node mkGeqOne(Node v);
};


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

