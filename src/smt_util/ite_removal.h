/*********************                                                        */
/*! \file ite_removal.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Kshitij Bansal, Tim King, Morgan Deters
 ** Minor contributors (to current version): Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Removal of term ITEs
 **
 ** Removal of term ITEs.
 **/

#include "cvc4_private.h"

#pragma once

#include <vector>
#include "expr/node.h"
#include "util/dump.h"
#include "context/context.h"
#include "context/cdinsert_hashmap.h"
#include "util/hash.h"
#include "util/bool.h"

namespace CVC4 {

namespace theory {
  class ContainsTermITEVisitor;
}/* CVC4::theory namespace */

typedef std::hash_map<Node, unsigned, NodeHashFunction> IteSkolemMap;

class RemoveITE {
  typedef context::CDInsertHashMap< std::pair<Node, bool>, Node, PairHashFunction<Node, bool, NodeHashFunction, BoolHashFunction> > ITECache;
  ITECache d_iteCache;


public:

  RemoveITE(context::UserContext* u);
  ~RemoveITE();

  /**
   * Removes the ITE nodes by introducing skolem variables. All
   * additional assertions are pushed into assertions. iteSkolemMap
   * contains a map from introduced skolem variables to the index in
   * assertions containing the new Boolean ite created in conjunction
   * with that skolem variable.
   *
   * With reportDeps true, report reasoning dependences to the proof
   * manager (for unsat cores).
   */
  void run(std::vector<Node>& assertions, IteSkolemMap& iteSkolemMap, bool reportDeps = false);

  /**
   * Removes the ITE from the node by introducing skolem
   * variables. All additional assertions are pushed into
   * assertions. iteSkolemMap contains a map from introduced skolem
   * variables to the index in assertions containing the new Boolean
   * ite created in conjunction with that skolem variable.
   */
  Node run(TNode node, std::vector<Node>& additionalAssertions,
           IteSkolemMap& iteSkolemMap, bool inQuant);

  /**
   * Substitute under node using pre-existing cache.  Do not remove
   * any ITEs not seen during previous runs.
   */
  Node replace(TNode node, bool inQuant = false) const;

  /** Returns true if e contains a term ite. */
  bool containsTermITE(TNode e) const;

  /** Returns the collected size of the caches. */
  size_t collectedCacheSizes() const;

  /** Garbage collects non-context dependent data-structures. */
  void garbageCollect();

  /** Return the RemoveITE's containsVisitor. */
  theory::ContainsTermITEVisitor* getContainsVisitor();

private:
  theory::ContainsTermITEVisitor* d_containsVisitor;

};/* class RemoveTTE */

}/* CVC4 namespace */
