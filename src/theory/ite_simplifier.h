/*********************                                                        */
/*! \file ite_simplifier.h
 ** \verbatim
 ** Original author: Clark Barrett
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simplifications for ITE expressions
 **
 ** This module implements preprocessing phases designed to simplify ITE
 ** expressions.  Based on:
 ** Kim, Somenzi, Jin.  Efficient Term-ITE Conversion for SMT.  FMCAD 2009.
 ** Burch, Jerry.  Techniques for Verifying Superscalar Microprocessors.  DAC '96
 **/

#include "cvc4_private.h"

#ifndef __CVC4__ITE_SIMPLIFIER_H
#define __CVC4__ITE_SIMPLIFIER_H

#include <vector>
#include <ext/hash_map>
#include <ext/hash_set>
#include "expr/node.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

class ITESimplifier {
private:
  Node d_true;
  Node d_false;

  typedef std::hash_map<Node, uint32_t, NodeHashFunction> HeightMap;
  HeightMap d_termITEHeight;

  typedef std::hash_set<Node, NodeHashFunction> NodeSet;

public:
  inline bool isTermITE(TNode e) const {
    return (e.getKind() == kind::ITE && !e.getType().isBoolean());
  }
  inline bool triviallyContainsNoTermITEs(TNode e) const {
    return e.isConst() || e.isVar();
  }

  /**
   * Compute and [potentially] cache the termITEHeight() of e.
   * The term ite height equals the maximum number of term ites
   * encountered on any path from e to a leaf.
   * Inductively:
   *  - termITEHeight(leaves) = 0
   *  - termITEHeight(e: term-ite(c, t, e) ) =
   *     1 + max(termITEHeight(t), termITEHeight(e)) ; Don't include c
   *  - termITEHeight(e not term ite) = max_{c in children(e)) (termITEHeight(c))
   */
  uint32_t termITEHeight(TNode e);

  /**
   * Safely looks up the term ite height of e.
   * If this is unknown (uncached and non-trivial), returns UINT32_MAX.
   */
  uint32_t lookupTermITEHeight(TNode e) const{
    if(triviallyContainsNoTermITEs(e)){
      return 0;
    }else{
      HeightMap::const_iterator pos = d_termITEHeight.find(e);
      if(pos == d_termITEHeight.end() ){
        return (*d_termITEHeight.find(e)).second;
      }else{
        return std::numeric_limits<uint32_t>::max();
      }
    }
  }

  /**
   * From the definition of termITEHeight(e),
   * e contains a term-ite iff termITEHeight(e) > 0
   */
  bool containsTermITE(TNode e){
    return termITEHeight(e) > 0;
  }

private:
  // ConstantIte is a small inductive sublanguage:
  //     constant
  // or  termITE(cnd, ConstantIte, ConstantIte)
  typedef std::vector<Node> NodeVec;
  typedef std::hash_map<Node, NodeVec*, NodeHashFunction > ConstantLeavesMap;
  ConstantLeavesMap d_constantLeaves;

  // Lists all of the vectors in d_constantLeaves for fast deletion.
  std::vector<NodeVec*> d_allocatedConstantLeaves;

  // d_constantLeaves satisfies the following invariants:
  // not containsTermITE(x) then !isKey(x)
  // containsTermITE(x):
  // - not isKey(x) then this value is uncomputed
  // - d_constantLeaves[x] == NULL, then this contains a non-constant leaf
  // - d_constantLeaves[x] != NULL, then this contains a sorted list of constant leaf
  bool isConstantIte(TNode e){
    if(e.isConst()){
      return true;
    }else if(isTermITE(e)){
      NodeVec* constants = computeConstantLeaves(e);
      return constants != NULL;
    }else{
      return false;
    }
  }
  NodeVec* computeConstantLeaves(TNode ite);
  Node transformAtom(TNode atom);
  Node attemptConstantRemoval(TNode atom);
  Node attemptLiftEquality(TNode atom);
  Node attemptEagerRemoval(TNode atom);

  // Searches for a fringe of a node where all leafs are constant ites,
  //bool searchConstantITEs(TNode f, std::vector<Node>& found, unsigned maxFound, int maxDepth);

  // Given ConstantIte trees lcite and rcite,
  // return a boolean expression eequivalent to (= lcite rcite)
  Node intersectConstantIte(TNode lcite, TNode rcite);

  // Given ConstantIte tree cite and a constant c,
  // return a boolean expression equivalent to (= lcite c)
  Node constantIteEqualsConstant(TNode cite, TNode c);

  typedef std::pair<Node, Node> NodePair;
  struct NodePairHashFunction {
    size_t operator () (const NodePair& pair) const {
      size_t hash = 0;
      hash = 0x9e3779b9 + NodeHashFunction().operator()(pair.first);
      hash ^= 0x9e3779b9 + NodeHashFunction().operator()(pair.second) + (hash << 6) + (hash >> 2);
      return hash;
    }
  };/* struct ITESimplifier::NodePairHashFunction */
  typedef std::hash_map<NodePair, Node, NodePairHashFunction> NodePairMap;
  NodePairMap d_constantIteEqualsConstantCache;
  NodePairMap d_replaceOverCache;
  NodePairMap d_replaceOverTermIteCache;
  Node replaceOver(Node n, Node replaceWith, Node simpVar);
  Node replaceOverTermIte(Node term, Node simpAtom, Node simpVar);

  std::hash_map<Node, bool, NodeHashFunction> d_leavesConstCache;
  bool leavesAreConst(TNode e, theory::TheoryId tid);
  bool leavesAreConst(TNode e);

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  typedef std::hash_map<TNode, Node, TNodeHashFunction> TNodeMap;


  NodePairMap d_simpConstCache;
  Node simpConstants(TNode simpContext, TNode iteNode, TNode simpVar);
  std::hash_map<TypeNode, Node, TypeNode::HashFunction> d_simpVars;
  Node getSimpVar(TypeNode t);

  NodeMap d_simpContextCache;
  Node createSimpContext(TNode c, Node& iteNode, Node& simpVar);

  Node simpITEAtom(TNode atom);

  NodeMap d_simpITECache;

public:
  Node simpITE(TNode assertion);

  bool shouldHeuristicallyClearCaches() const;
  void clearSimpITECaches();

private:

  class CareSetPtr;
  class CareSetPtrVal {
    friend class ITESimplifier::CareSetPtr;
    ITESimplifier& d_iteSimplifier;
    unsigned d_refCount;
    std::set<Node> d_careSet;
    CareSetPtrVal(ITESimplifier& simp) : d_iteSimplifier(simp), d_refCount(1) {}
  };

  std::vector<CareSetPtrVal*> d_usedSets;
  void careSetPtrGC(CareSetPtrVal* val) {
    d_usedSets.push_back(val);
  }

  class CareSetPtr {
    CareSetPtrVal* d_val;
    CareSetPtr(CareSetPtrVal* val) : d_val(val) {}
  public:
    CareSetPtr() : d_val(NULL) {}
    CareSetPtr(const CareSetPtr& cs) {
      d_val = cs.d_val;
      if (d_val != NULL) {
        ++(d_val->d_refCount);
      }
    }
    ~CareSetPtr() {
      if (d_val != NULL && (--(d_val->d_refCount) == 0)) {
        d_val->d_iteSimplifier.careSetPtrGC(d_val);
      }
    }
    CareSetPtr& operator=(const CareSetPtr& cs) {
      if (d_val != cs.d_val) {
        if (d_val != NULL && (--(d_val->d_refCount) == 0)) {
          d_val->d_iteSimplifier.careSetPtrGC(d_val);
        }
        d_val = cs.d_val;
        if (d_val != NULL) {
          ++(d_val->d_refCount);
        }
      }
      return *this;
    }
    std::set<Node>& getCareSet() { return d_val->d_careSet; }
    static CareSetPtr mkNew(ITESimplifier& simp) {
      CareSetPtrVal* val = new CareSetPtrVal(simp);
      return CareSetPtr(val);
    }
    static CareSetPtr recycle(CareSetPtrVal* val) {
      Assert(val != NULL && val->d_refCount == 0);
      val->d_refCount = 1;
      return CareSetPtr(val);
    }
  };

  CareSetPtr getNewSet();

  typedef std::map<TNode, CareSetPtr> CareMap;
  void updateQueue(CareMap& queue, TNode e, CareSetPtr& careSet);
  Node substitute(TNode e, TNodeMap& substTable, TNodeMap& cache);

public:
  Node simplifyWithCare(TNode e);


  ITESimplifier();
  ~ITESimplifier();

private:

  class Statistics {
  public:
    IntStat d_maxNonConstantsFolded;
    IntStat d_unexpected;
    IntStat d_unsimplified;
    IntStat d_exactMatchFold;
    IntStat d_binaryPredFold;
    IntStat d_specialEqualityFolds;
    IntStat d_simpITEVisits;

    HistogramStat<uint32_t> d_inSmaller;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif
