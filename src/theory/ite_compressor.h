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

#ifndef __CVC4__ITE_COMPRESSOR_H
#define __CVC4__ITE_COMPRESSOR_H

#include <vector>
#include <ext/hash_map>
#include <ext/hash_set>
#include "expr/node.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

class ITECompressor {
public:
  ITECompressor();
  ~ITECompressor();

  /* returns false if an assertion is discovered to be equal to false. */
  bool compress(std::vector<Node>& assertions);

  /* garbage Collects the compressor. */
  void garbageCollect();

private:
  Node d_true;
  Node d_false;

  typedef std::hash_map<Node, uint32_t, NodeHashFunction> NodeCountMap;
  typedef std::hash_set<Node, NodeHashFunction> NodeSet;


  /**
   * From the definition of termITEHeight(e),
   * e contains a term-ite iff termITEHeight(e) > 0
   */
  bool debugContainsTermITE(TNode e);
  typedef std::hash_map<Node, bool, NodeHashFunction> NodeBoolMap;
  NodeBoolMap d_debugContainsTermITECache;


  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  typedef std::hash_map<TNode, Node, TNodeHashFunction> TNodeMap;

private:
  void reset();
  NodeCountMap d_reachCount;
  std::vector<Node>* d_assertions;
  NodeMap d_compressed;

  void computeReachability(const std::vector<Node>& assertions);

  Node push_back_boolean(Node original, Node compressed);
  bool multipleParents(TNode c);
  Node compressBooleanITEs(Node toCompress);
  Node compressTerm(Node toCompress);
  Node compressBoolean(Node toCompress);

  class Statistics {
  public:
    IntStat d_compressCalls;
    IntStat d_skolemsAdded;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif
