/*********************                                                        */
/*! \file ite_simplifier.cpp
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


#include "theory/ite_simplifier.h"

//#include <deque>
#include <utility>

//#include "prop/prop_engine.h"
//#include "expr/command.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
//#include "context/cdhashset.h"
//#include "util/hash.h"
//#include "util/cache.h"
//#include "theory/shared_terms_database.h"
//#include "theory/term_registration_visitor.h"
//#include "theory/valuation.h"


using namespace std;
using namespace CVC4;
using namespace theory;

bool ITESimplifier::leavesAreConst(TNode e){
  return leavesAreConst(e, theory::Theory::theoryOf(e));
}

// Goals:
// 1. Determine when to lift ites for kind benchmarks
//  x = ite(blah) t e :-> ite(blah) (x(15) = t) (x(15) = e)
//  x has to not be a bitvector/uf/real variable
//    applications, integers, are fine.
// 2. NEC lib benchmarks with tons of constant ites.
//   15 = (ite with constant leaves ... )
//   (ite with constant leaves ... ) = (ite with constant leaves ... )
// 3. formula contains no term ites
//   Optimize ite_removal.cpp
//
// Collect the following information:
// - term ite height:
//  height 0 - t e
//  height 1 - q : ite(c t e)
//  height 2 - p : ite(c q e), r : ite(c q t)
//  height 3 - s : ite((q = p) t e),  u: ite(c r e)
// term ite height 0 <=>contains no term ites
// term ite height >0 is a requirement for constant leaf ites
ITESimplifier::ITESimplifier() {
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

ITESimplifier::~ITESimplifier() {
  clearSimpITECaches();
  Assert(d_constantLeaves.empty());
  Assert(d_allocatedConstantLeaves.empty());
}

void ITESimplifier::clearSimpITECaches(){
  Chat() << "clear ite caches " << endl;
  for(size_t i = 0, N = d_allocatedConstantLeaves.size(); i < N; ++i){
    NodeVec* curr = d_allocatedConstantLeaves[i];
    delete curr;
  }
  d_constantLeaves.clear();
  d_allocatedConstantLeaves.clear();
  d_termITEHeight.clear();
  d_constantIteEqualsConstantCache.clear();
  d_replaceOverCache.clear();
  d_replaceOverTermIteCache.clear();
  d_simpITECache.clear();
  d_simpVars.clear();
  d_simpConstCache.clear();
  d_leavesConstCache.clear();
  d_simpContextCache.clear();
}

bool ITESimplifier::shouldHeuristicallyClearCaches() const {
  static const size_t SIZE_BOUND = 1000;
  Chat() << "simpITECache size " << d_simpITECache.size() << endl;
  return options::simpIteClearCache() && (d_simpITECache.size() > SIZE_BOUND);
}

ITESimplifier::Statistics::Statistics():
  d_maxNonConstantsFolded("ite-simp::maxNonConstantsFolded", 0),
  d_unexpected("ite-simp::unexpected", 0),
  d_unsimplified("ite-simp::unsimplified", 0),
  d_exactMatchFold("ite-simp::exactMatchFold", 0),
  d_binaryPredFold("ite-simp::binaryPredFold", 0),
  d_specialEqualityFolds("ite-simp::specialEqualityFolds", 0),
  d_simpITEVisits("ite-simp::simpITE.visits", 0),
  d_inSmaller("ite-simp::inSmaller")
{
  StatisticsRegistry::registerStat(&d_maxNonConstantsFolded);
  StatisticsRegistry::registerStat(&d_unexpected);
  StatisticsRegistry::registerStat(&d_unsimplified);
  StatisticsRegistry::registerStat(&d_exactMatchFold);
  StatisticsRegistry::registerStat(&d_binaryPredFold);
  StatisticsRegistry::registerStat(&d_specialEqualityFolds);
  StatisticsRegistry::registerStat(&d_simpITEVisits);
  StatisticsRegistry::registerStat(&d_inSmaller);
}

ITESimplifier::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_maxNonConstantsFolded);
  StatisticsRegistry::unregisterStat(&d_unexpected);
  StatisticsRegistry::unregisterStat(&d_unsimplified);
  StatisticsRegistry::unregisterStat(&d_exactMatchFold);
  StatisticsRegistry::unregisterStat(&d_binaryPredFold);
  StatisticsRegistry::unregisterStat(&d_specialEqualityFolds);
  StatisticsRegistry::unregisterStat(&d_simpITEVisits);
  StatisticsRegistry::unregisterStat(&d_inSmaller);
}
struct StackElement {
  TNode curr;
  unsigned pos;
  uint32_t maxChildHeight;
  StackElement(){}
  StackElement(TNode c) : curr(c), pos(0), maxChildHeight(0){ }
};
uint32_t ITESimplifier::termITEHeight(TNode e){

  if(triviallyContainsNoTermITEs(e)){ return 0; }

  HeightMap::const_iterator end = d_termITEHeight.end();
  HeightMap::const_iterator tmp_it = d_termITEHeight.find(e);
  if(tmp_it != end){
    return (*tmp_it).second;
  }


  uint32_t returnValue = 0;
  // This is initially 0 as the very first call this is included in the max,
  // but this has no effect.
  std::vector<StackElement> stack;
  stack.push_back(StackElement(e));
  while(!stack.empty()){
    StackElement& top = stack.back();
    top.maxChildHeight = std::max(top.maxChildHeight, returnValue);
    TNode curr = top.curr;
    if(top.pos >= curr.getNumChildren()){
      // done with the current node
      returnValue = top.maxChildHeight + (isTermITE(curr) ? 1 : 0);
      d_termITEHeight[curr] = returnValue;
      stack.pop_back();
      continue;
    }else{
      if(top.pos == 0 && curr.getKind() == kind::ITE){
        ++top.pos;
        returnValue = 0;
        continue;
      }
      // this is someone's child
      TNode child = curr[top.pos];
      ++top.pos;
      if(triviallyContainsNoTermITEs(child)){
        returnValue = 0;
      }else{
        tmp_it = d_termITEHeight.find(child);
        if(tmp_it != end){
          returnValue = (*tmp_it).second;
        }else{
          stack.push_back(StackElement(child));
        }
      }
    }
  }
  return returnValue;
}


ITESimplifier::NodeVec* ITESimplifier::computeConstantLeaves(TNode ite){
  Assert(isTermITE(ite));
  ConstantLeavesMap::const_iterator it = d_constantLeaves.find(ite);
  ConstantLeavesMap::const_iterator end = d_constantLeaves.end();
  if(it != end){
    return (*it).second;
  }
  TNode thenB = ite[1];
  TNode elseB = ite[2];

  // special case 2 constant children
  if(thenB.isConst() && elseB.isConst()){
    NodeVec* pair = new NodeVec(2);
    (*pair)[0] = std::min(thenB, elseB);
    (*pair)[1] = std::max(thenB, elseB);
    d_constantLeaves[ite] = pair;
    return pair;
  }
  // At least 1 is an ITE
  if(!(thenB.isConst() || thenB.getKind() == kind::ITE) ||
     !(elseB.isConst() || elseB.getKind() == kind::ITE)){
    // Cannot be a termITE tree
    d_constantLeaves[ite] = NULL;
    return NULL;
  }

  // At least 1 is not a constant
  TNode definitelyITE = thenB.isConst() ? elseB : thenB;
  TNode maybeITE = thenB.isConst() ? thenB : elseB;

  NodeVec* defChildren = computeConstantLeaves(definitelyITE);
  if(defChildren == NULL){
    d_constantLeaves[ite] = NULL;
    return NULL;
  }

  NodeVec scratch;
  NodeVec* maybeChildren = NULL;
  if(maybeITE.getKind() == kind::ITE){
    maybeChildren = computeConstantLeaves(maybeITE);
  }else{
    scratch.push_back(maybeITE);
    maybeChildren = &scratch;
  }
  if(maybeChildren == NULL){
    d_constantLeaves[ite] = NULL;
    return NULL;
  }

  NodeVec* both = new NodeVec(defChildren->size()+maybeChildren->size());
  NodeVec::iterator newEnd;
  newEnd = std::set_union(defChildren->begin(), defChildren->end(),
                          maybeChildren->begin(), maybeChildren->end(),
                          both->begin());
  both->resize(newEnd - both->begin());
  d_constantLeaves[ite] = both;
  return both;
}

// This is uncached! Better for protoyping or getting limited size examples
struct IteTreeSearchData{
  set<Node> visited;
  set<Node> constants;
  set<Node> nonConstants;
  int maxConstants;
  int maxNonconstants;
  int maxDepth;
  bool failure;
  IteTreeSearchData()
    : maxConstants(-1), maxNonconstants(-1), maxDepth(-1), failure(false)
  {}
};
void iteTreeSearch(Node e, int depth, IteTreeSearchData& search){
  if(search.maxDepth >= 0 && depth > search.maxDepth){
    search.failure = true;
  }
  if(search.failure){
    return;
  }
  if(search.visited.find(e) != search.visited.end()){
    return;
  }else{
    search.visited.insert(e);
  }

  if(e.isConst()){
    search.constants.insert(e);
    if(search.maxConstants >= 0 &&
       search.constants.size() > (unsigned)search.maxConstants){
      search.failure = true;
    }
  }else if(e.getKind() == kind::ITE){
    iteTreeSearch(e[1], depth+1, search);
    iteTreeSearch(e[2], depth+1, search);
  }else{
    search.nonConstants.insert(e);
    if(search.maxNonconstants >= 0 &&
       search.nonConstants.size() > (unsigned)search.maxNonconstants){
      search.failure = true;
    }
  }
}

Node ITESimplifier::replaceOver(Node n, Node replaceWith, Node simpVar){
  if(n == simpVar){
    return replaceWith;
  }else if(n.getNumChildren() == 0){
    return n;
  }
  Assert(n.getNumChildren() > 0);
  Assert(!n.isVar());

  pair<Node, Node> p = make_pair(n, replaceWith);
  if(d_replaceOverCache.find(p) != d_replaceOverCache.end()){
    return d_replaceOverCache[p];
  }

  NodeBuilder<> builder(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << n.getOperator();
  }
  unsigned i = 0;
  for (; i < n.getNumChildren(); ++ i) {
    Node newChild = replaceOver(n[i], replaceWith, simpVar);
    builder << newChild;
  }
  // Mark the substitution and continue
  Node result = builder;
  d_replaceOverCache[p] = result;
  return result;
}

Node ITESimplifier::replaceOverTermIte(Node e, Node simpAtom, Node simpVar){
  if(e.getKind() == kind::ITE){
    pair<Node, Node> p = make_pair(e, simpAtom);
    if(d_replaceOverTermIteCache.find(p) != d_replaceOverTermIteCache.end()){
      return d_replaceOverTermIteCache[p];
    }
    Assert(!e.getType().isBoolean());
    Node cnd = e[0];
    Node newThen = replaceOverTermIte(e[1], simpAtom, simpVar);
    Node newElse = replaceOverTermIte(e[2], simpAtom, simpVar);
    Node newIte = cnd.iteNode(newThen, newElse);
    d_replaceOverTermIteCache[p] = newIte;
    return newIte;
  }else{
    return replaceOver(simpAtom, e, simpVar);
  }
}

TNode uniqueNonConstant(TNode term){
  if(term.getKind() == kind::ITE ||
     term.isVar() ||
     term.getKind() == kind::APPLY_UF){
    #warning "Don't commit to trunk"
    return term;
  }else if(term.getNumChildren() == 0){
    return Node::null();
  }else{
    TNode found = Node::null();
    for(unsigned i =0, N = term.getNumChildren(); i < N; ++i){
      TNode child = term[i];
      if(!child.isConst()){
        TNode fromChild = uniqueNonConstant(child);
        if(fromChild.isNull()){
          return Node::null();
        }else if(found.isNull()){
          found = fromChild;
        }else{
          return Node::null();
        }
      }
    }
    return found;
  }
}

Node ITESimplifier::attemptLiftEquality(TNode atom){
  if(atom.getKind() == kind::EQUAL){
    TNode left = atom[0];
    TNode right = atom[1];
    if((left.getKind() == kind::ITE || right.getKind() == kind::ITE)&&
       !(left.getKind() == kind::ITE && right.getKind() == kind::ITE)){

      // exactly 1 is an ite
      TNode ite = left.getKind() == kind::ITE ? left :right;
      TNode notIte = left.getKind() == kind::ITE ? right : left;

      if(notIte == ite[1]){
        ++(d_statistics.d_exactMatchFold);
        return ite[0].iteNode(d_true, notIte.eqNode(ite[2]));
      }else if(notIte == ite[2]){
        ++(d_statistics.d_exactMatchFold);
        return ite[0].iteNode(notIte.eqNode(ite[1]), d_true);
      }
      if(notIte.isConst() &&
         (ite[1].isConst() || ite[2].isConst())){
        ++(d_statistics.d_exactMatchFold);
        return ite[0].iteNode(notIte.eqNode(ite[1]),  notIte.eqNode(ite[2]));
      }
    }
  }

  // try a similar more relaxed version for non-equality operators
  if(atom.getMetaKind() == kind::metakind::OPERATOR &&
     atom.getNumChildren() == 2 &&
     !atom[1].getType().isBoolean()){

    TNode left = atom[0];
    TNode right = atom[1];
    if( (left.getKind() == kind::ITE || right.getKind() == kind::ITE)&&
       !(left.getKind() == kind::ITE && right.getKind() == kind::ITE)){
      // exactly 1 is an ite
      bool leftIsIte = left.getKind() == kind::ITE;
      Node ite = leftIsIte ? left :right;
      Node notIte = leftIsIte ? right : left;

      if(notIte.isConst()){
        IteTreeSearchData search;
        search.maxNonconstants = 2;
        iteTreeSearch(ite, 0, search);
        if(!search.failure){
          d_statistics.d_maxNonConstantsFolded.maxAssign(search.nonConstants.size());
          Debug("ite::simpite") << "used " << search.nonConstants.size() << " nonconstants" << endl;
          NodeManager* nm = NodeManager::currentNM();
          Node simpVar = getSimpVar(notIte.getType());
          TNode newLeft = leftIsIte  ? simpVar : notIte;
          TNode newRight = leftIsIte ? notIte : simpVar;
          Node newAtom = nm->mkNode(atom.getKind(), newLeft, newRight);

          ++(d_statistics.d_binaryPredFold);
          return replaceOverTermIte(ite, newAtom, simpVar);
        }
      }
    }
  }
#warning "This is way too tailored. Must generalize!"
  if(atom.getKind() == kind::EQUAL &&
     atom.getNumChildren() == 2 &&
     isTermITE(atom[0]) &&
     atom[1].getKind() == kind::MULT &&
     atom[1].getNumChildren() == 2 &&
     atom[1][0].isConst() &&
     atom[1][0].getConst<Rational>().isNegativeOne() &&
     isTermITE(atom[1][1]) &&
     termITEHeight(atom[0]) == 1 &&
     termITEHeight(atom[1][1]) == 1 &&
     (atom[0][1].isConst() || atom[0][2].isConst()) &&
     (atom[1][1][1].isConst() || atom[1][1][2].isConst()) ){
    // expand all 4 cases

    Node negOne = atom[1][0];

    Node lite = atom[0];
    Node lC = lite[0];
    Node lT = lite[1];
    Node lE = lite[2];

    NodeManager* nm = NodeManager::currentNM();
    Node negRite = atom[1][1];
    Node rC = negRite[0];
    Node rT = nm->mkNode(kind::MULT, negOne, negRite[1]);
    Node rE = nm->mkNode(kind::MULT, negOne, negRite[2]);

    // (ite lC lT lE) = (ite rC rT rE)
    // (ite lc (= lT (ite rC rT rE) (= lE (ite rC rT rE))))
    // (ite lc (ite rC (= lT rT) (= lT rE))
    //         (ite rC (= lE rT) (= lE rE)))

    Node eqTT = lT.eqNode(rT);
    Node eqTE = lT.eqNode(rE);
    Node eqET = lE.eqNode(rT);
    Node eqEE = lE.eqNode(rE);
    Node thenLC = rC.iteNode(eqTT, eqTE);
    Node elseLC = rC.iteNode(eqET, eqEE);
    Node newIte = lC.iteNode(thenLC, elseLC);

    ++(d_statistics.d_specialEqualityFolds);
    return newIte;
  }
  return Node::null();
}

// Interesting classes of atoms:
// 2. Contains constants and 1 constant term ite
// 3. Contains 2 constant term ites
Node ITESimplifier::transformAtom(TNode atom){
  uint32_t h = termITEHeight(atom);
  if(h == 0){
    //d_iteRemover.markAsNoTermITESubNodes(atom);
    return Node::null();
  }else{
    Node acr = attemptConstantRemoval(atom);
    if(!acr.isNull()){
      return acr;
    }
    Node ale = attemptLiftEquality(atom);
    if(!ale.isNull()){
      //return ale;
    }
    return Node::null();
  }
}

// if true, the search encountered a not okay term
// bool ITESimplifier::searchConstantITEs(TNode f, std::vector<Node>& found, unsigned maxFound, int maxDepth){
//   if(f.isConst()){
//     found.push_back(f);
//     return found.size() < maxFound;
//   }else if(f.getKind() == kind::ITE){
//     if(isConstantITE(f)){
//       found.push_back(f);
//       return found.size() < maxFound;
//     }else{
//       return true;
//     }
//   }else if(f.getNumChildren() > 0){
//     if(f is parametric){
//       return false;
//     }else if(maxDepth >= 0){
//       bool res = false;
//       TNode::iterator it = f.begin(), f.end();
//       for(; it != end && !res; ++it){
//         res = searchConstantITEs(*it, found, maxFound, maxDepth-1);
//       }
//       return res;
//     }else{
//       return false;
//     }
//   }else{
//     return false;
//   }
// }

Node ITESimplifier::constantIteEqualsConstant(TNode cite, TNode constant){
  static int instance = 0;
  ++instance;
  Debug("ite::constantIteEqualsConstant") << instance << "constantIteEqualsConstant("<<cite << ", " << constant<<")"<< endl;
  if(cite.isConst()){
    Node res = (cite == constant) ? d_true : d_false;
    Debug("ite::constantIteEqualsConstant") << instance << "->" << res << endl;
    return res;
  }
  std::pair<Node,Node> pair = make_pair(cite, constant);

  NodePairMap::const_iterator eq_pos = d_constantIteEqualsConstantCache.find(pair);
  if(eq_pos != d_constantIteEqualsConstantCache.end()){
    Debug("ite::constantIteEqualsConstant") << instance << "->" << (*eq_pos).second << endl;
    return (*eq_pos).second;
  }

  NodeVec* leaves = computeConstantLeaves(cite);
  Assert(leaves != NULL);
  if(std::binary_search(leaves->begin(), leaves->end(), constant)){
    if(leaves->size() == 1){
      // probably unreachable
      d_constantIteEqualsConstantCache[pair] = d_true;
      Debug("ite::constantIteEqualsConstant") << instance << "->" << d_true << endl;
      return d_true;
    }else{
      Assert(cite.getKind() == kind::ITE);
      TNode cnd = cite[0];
      TNode tB = cite[1];
      TNode fB = cite[2];
      Node tEqs = constantIteEqualsConstant(tB, constant);
      Node fEqs = constantIteEqualsConstant(fB, constant);
      Node boolIte = cnd.iteNode(tEqs, fEqs);
      d_constantIteEqualsConstantCache[pair] = boolIte;
      //Debug("ite::constantIteEqualsConstant") << instance << "->" << boolIte << endl;
      return boolIte;
    }
  }else{
    d_constantIteEqualsConstantCache[pair] = d_false;
    Debug("ite::constantIteEqualsConstant") << instance << "->" << d_false << endl;
    return d_false;
  }
}

Node ITESimplifier::intersectConstantIte(TNode lcite, TNode rcite){
  // intersect the constant ite trees lcite and rcite

  if(lcite.isConst()){
    (d_statistics.d_inSmaller)<< 1;
    return constantIteEqualsConstant(rcite, lcite);
  }
  if(rcite.isConst()){
    (d_statistics.d_inSmaller)<< 1;
    return constantIteEqualsConstant(lcite, rcite);
  }
  Assert(lcite.getKind() == kind::ITE);
  Assert(rcite.getKind() == kind::ITE);

  NodeVec* leftValues = computeConstantLeaves(lcite);
  NodeVec* rightValues = computeConstantLeaves(rcite);

  uint32_t smaller = std::min(leftValues->size(), rightValues->size());
  (d_statistics.d_inSmaller)<< smaller;

  NodeVec intersection(std::max(leftValues->size(), leftValues->size()));
  NodeVec::iterator newEnd;
  newEnd = std::set_intersection(leftValues->begin(), leftValues->end(),
                                 rightValues->begin(), rightValues->end(),
                                 intersection.begin());
  intersection.resize(newEnd - intersection.begin());
  if(intersection.empty()){
    return d_false;
  }else{
    NodeBuilder<> nb(kind::OR);
    NodeVec::const_iterator it = intersection.begin(), end=intersection.end();
    for(; it != end; ++it){
      Node inBoth = *it;
      Node lefteq = constantIteEqualsConstant(lcite, inBoth);
      Node righteq = constantIteEqualsConstant(rcite, inBoth);
      Node bothHold = lefteq.andNode(righteq);
      nb << bothHold;
    }
    Node result = (nb.getNumChildren() >= 1) ? (Node)nb : nb[0];
    return result;
  }
}

Node ITESimplifier::attemptEagerRemoval(TNode atom){
  if(atom.getKind() == kind::EQUAL){
    TNode left = atom[0];
    TNode right = atom[1];
    if((left.isConst() &&
        right.getKind() == kind::ITE && isConstantIte(right)) ||
       (right.isConst() &&
        left.getKind() == kind::ITE && isConstantIte(left))){
      TNode constant = left.isConst() ? left : right;
      TNode cite = left.isConst() ? right : left;

      std::pair<Node,Node> pair = make_pair(cite, constant);
      NodePairMap::const_iterator eq_pos = d_constantIteEqualsConstantCache.find(pair);
      if(eq_pos != d_constantIteEqualsConstantCache.end()){
        Node ret = (*eq_pos).second;
        if(ret.isConst()){
          return ret;
        }else{
          return Node::null();
        }
      }

      NodeVec* leaves = computeConstantLeaves(cite);
      Assert(leaves != NULL);
      if(!std::binary_search(leaves->begin(), leaves->end(), constant)){
        std::pair<Node,Node> pair = make_pair(cite, constant);
        d_constantIteEqualsConstantCache[pair] = d_false;
        return d_false;
      }
    }
  }
  return Node::null();
}

Node ITESimplifier::attemptConstantRemoval(TNode atom){
  if(atom.getKind() == kind::EQUAL){
    TNode left = atom[0];
    TNode right = atom[1];
    if(isConstantIte(left) && isConstantIte(right)){
      return intersectConstantIte(left, right);
    }
  }
  return Node::null();
}


bool ITESimplifier::leavesAreConst(TNode e, TheoryId tid)
{
  Assert((e.getKind() == kind::ITE && !e.getType().isBoolean()) ||
         Theory::theoryOf(e) != THEORY_BOOL);
  if (e.isConst()) {
    return true;
  }

  hash_map<Node, bool, NodeHashFunction>::iterator it;
  it = d_leavesConstCache.find(e);
  if (it != d_leavesConstCache.end()) {
    return (*it).second;
  }

  if (!containsTermITE(e) && Theory::isLeafOf(e, tid)) {
    d_leavesConstCache[e] = false;
    return false;
  }

  Assert(e.getNumChildren() > 0);
  size_t k = 0, sz = e.getNumChildren();

  if (e.getKind() == kind::ITE) {
    k = 1;
  }

  for (; k < sz; ++k) {
    if (!leavesAreConst(e[k], tid)) {
      d_leavesConstCache[e] = false;
      return false;
    }
  }
  d_leavesConstCache[e] = true;
  return true;
}


Node ITESimplifier::simpConstants(TNode simpContext, TNode iteNode, TNode simpVar)
{
  NodePairMap::iterator it;
  it = d_simpConstCache.find(pair<Node, Node>(simpContext,iteNode));
  if (it != d_simpConstCache.end()) {
    return (*it).second;
  }

  if (iteNode.getKind() == kind::ITE) {
    NodeBuilder<> builder(kind::ITE);
    builder << iteNode[0];
    unsigned i = 1;
    for (; i < iteNode.getNumChildren(); ++ i) {
      Node n = simpConstants(simpContext, iteNode[i], simpVar);
      if (n.isNull()) {
        return n;
      }
      builder << n;
    }
    // Mark the substitution and continue
    Node result = builder;
    result = Rewriter::rewrite(result);
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = result;
    return result;
  }

  if (!containsTermITE(iteNode)) {
    Node n = Rewriter::rewrite(simpContext.substitute(simpVar, iteNode));
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
    return n;
  }

  Node iteNode2;
  Node simpVar2;
  d_simpContextCache.clear();
  Node simpContext2 = createSimpContext(iteNode, iteNode2, simpVar2);
  if (!simpContext2.isNull()) {
    Assert(!iteNode2.isNull());
    simpContext2 = simpContext.substitute(simpVar, simpContext2);
    Node n = simpConstants(simpContext2, iteNode2, simpVar2);
    if (n.isNull()) {
      return n;
    }
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
    return n;
  }
  return Node();
}


Node ITESimplifier::getSimpVar(TypeNode t)
{
  std::hash_map<TypeNode, Node, TypeNode::HashFunction>::iterator it;
  it = d_simpVars.find(t);
  if (it != d_simpVars.end()) {
    return (*it).second;
  }
  else {
    Node var = NodeManager::currentNM()->mkSkolem("iteSimp_$$", t, "is a variable resulting from ITE simplification");
    d_simpVars[t] = var;
    return var;
  }
}


Node ITESimplifier::createSimpContext(TNode c, Node& iteNode, Node& simpVar)
{
  NodeMap::iterator it;
  it = d_simpContextCache.find(c);
  if (it != d_simpContextCache.end()) {
    return (*it).second;
  }

  if (!containsTermITE(c)) {
    d_simpContextCache[c] = c;
    return c;
  }

  if (c.getKind() == kind::ITE && !c.getType().isBoolean()) {
    // Currently only support one ite node in a simp context
    // Return Null if more than one is found
    if (!iteNode.isNull()) {
      return Node();
    }
    simpVar = getSimpVar(c.getType());
    if (simpVar.isNull()) {
      return Node();
    }
    d_simpContextCache[c] = simpVar;
    iteNode = c;
    return simpVar;
  }

  NodeBuilder<> builder(c.getKind());
  if (c.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << c.getOperator();
  }
  unsigned i = 0;
  for (; i < c.getNumChildren(); ++ i) {
    Node newChild = createSimpContext(c[i], iteNode, simpVar);
    if (newChild.isNull()) {
      return newChild;
    }
    builder << newChild;
  }
  // Mark the substitution and continue
  Node result = builder;
  d_simpContextCache[c] = result;
  return result;
}
typedef std::hash_set<Node, NodeHashFunction> NodeSet;
void countReachable_(Node x, Kind k, NodeSet& visited, uint32_t& reached){
  if(visited.find(x) != visited.end()){
    return;
  }
  visited.insert(x);
  if(x.getKind() == k){
    ++reached;
  }
  for(unsigned i =0, N=x.getNumChildren(); i < N; ++i){
    countReachable_(x[i], k, visited, reached);
  }
}

uint32_t countReachable(TNode x, Kind k){
  NodeSet visited;
  uint32_t reached = 0;
  countReachable_(x, k, visited, reached);
  return reached;
}

Node ITESimplifier::simpITEAtom(TNode atom)
{
  static int instance = 0;
  instance++;

  //cout << "still simplifying " << instance << endl;
  Node attempt = transformAtom(atom);
  //cout << "  finished " << instance << endl;
  if(!attempt.isNull()){
    Node rewritten = Rewriter::rewrite(attempt);
    Debug("ite::print-success")
      << instance << " "
      << "rewriting " << countReachable(rewritten, kind::ITE)
      <<  " from " <<  countReachable(atom, kind::ITE) << endl
      << "\t rewritten " << rewritten << endl
      << "\t input " << atom << endl;

    if(instance % 10 == 0) {
    }
    return rewritten;
  }
  if (leavesAreConst(atom)) {
    Node iteNode;
    Node simpVar;
    d_simpContextCache.clear();
    Node simpContext = createSimpContext(atom, iteNode, simpVar);
    if (!simpContext.isNull()) {
      if (iteNode.isNull()) {
        Assert(leavesAreConst(simpContext) && !containsTermITE(simpContext));
        ++(d_statistics.d_unexpected);
        Debug("ite::simpite") << instance << " "
                              << "how about?" << atom << endl;
        Debug("ite::simpite") << instance << " "
                              << "\t" << simpContext << endl;
        return Rewriter::rewrite(simpContext);
      }
      Node n = simpConstants(simpContext, iteNode, simpVar);
      if (!n.isNull()) {
        ++(d_statistics.d_unexpected);
        Debug("ite::simpite") << instance << " "
                              << "here?" << atom << endl;
        Debug("ite::simpite") << instance << " "
                              << "\t" << n << endl;
        return n;
      }
    }
  }
  if(Debug.isOn("ite::simpite")){
    if(countReachable(atom, kind::ITE) > 0){
      Debug("ite::simpite") << instance << " "
                            << "remaining " << atom << endl;
    }
  }
  ++(d_statistics.d_unsimplified);
  return atom;
}


struct preprocess_stack_element {
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct preprocess_stack_element */


Node ITESimplifier::simpITE(TNode assertion)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  static int call = 0;
  ++call;
  int iteration = 0;

  while (!toVisit.empty())
  {
    iteration ++;
    //cout << "call  " << call << " : " << iteration << endl;
    // The current node we are processing
    preprocess_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    // If node has no ITE's or already in the cache we're done, pop from the stack
    if (current.getNumChildren() == 0 ||
        (Theory::theoryOf(current) != THEORY_BOOL && !containsTermITE(current))) {
       d_simpITECache[current] = current;
       ++(d_statistics.d_simpITEVisits);
       toVisit.pop_back();
       continue;
    }

    NodeMap::iterator find = d_simpITECache.find(current);
    if (find != d_simpITECache.end()) {
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.children_added) {
      // Children have been processed, so substitute
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
        Assert(d_simpITECache.find(current[i]) != d_simpITECache.end());
        Node child = current[i];
        Node childRes = d_simpITECache[current[i]];
        if(child != childRes && childRes.isConst()){
          static int instance = 0;
          //cout << instance << " " << childRes << " " << i << current.getKind() << current << endl;
        }
        builder << childRes;
      }
      // Mark the substitution and continue
      Node result = builder;

      // If this is an atom, we process it
      if (Theory::theoryOf(result) != THEORY_BOOL &&
          result.getType().isBoolean()) {
        result = simpITEAtom(result);
      }

      if(current != result && result.isConst()){
        static int instance = 0;
        //cout << instance << " " << result << current << endl;
      }

      result = Rewriter::rewrite(result);
      d_simpITECache[current] = result;
      ++(d_statistics.d_simpITEVisits);
      toVisit.pop_back();
    } else if(options::simpCndBeforeBranch() && current.getKind() == kind::ITE) {
      TNode cnd = current[0];
      TNode tB = current[1];
      TNode eB = current[2];
      Node simpCnd = simpITE(cnd);

      if(simpCnd.isConst()){
        TNode selected = (simpCnd == d_true) ? tB : eB;
        Node simpSelected = simpITE(selected);
        d_simpITECache[current] = simpSelected;
        ++(d_statistics.d_simpITEVisits);
        toVisit.pop_back();
      }else{
        stackHead.children_added = true;
        NodeMap::iterator childFind = d_simpITECache.find(tB);
        if (childFind == d_simpITECache.end()) {
          toVisit.push_back(tB);
        }
        childFind = d_simpITECache.find(eB);
        if (childFind == d_simpITECache.end()) {
          toVisit.push_back(eB);
        }
      }
    } else {
      if(options::simpAtomsEarly() &&
         (Theory::theoryOf(current) != THEORY_BOOL &&
          current.getType().isBoolean())) {
        Node attempt = attemptEagerRemoval(current);
        if(!attempt.isNull() && attempt.isConst()){
          static int workedcount = 0;
          ++workedcount;
          if(workedcount % 200 == 0){
            Chat() << "worked " << workedcount << endl;
          }
          Node moreSimp = (attempt.isConst()) ? attempt : simpITE(attempt);
          d_simpITECache[current] = moreSimp;
          ++(d_statistics.d_simpITEVisits);
          toVisit.pop_back();
          continue;
        }
      }
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = d_simpITECache.find(childNode);
          if (childFind == d_simpITECache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // No children, so we're done
        d_simpITECache[current] = current;
        ++(d_statistics.d_simpITEVisits);
        toVisit.pop_back();
      }
    }
  }
  return d_simpITECache[assertion];
}


ITESimplifier::CareSetPtr ITESimplifier::getNewSet()
{
  if (d_usedSets.empty()) {
    return ITESimplifier::CareSetPtr::mkNew(*this);
  }
  else {
    ITESimplifier::CareSetPtr cs = ITESimplifier::CareSetPtr::recycle(d_usedSets.back());
    cs.getCareSet().clear();
    d_usedSets.pop_back();
    return cs;
  }
}


void ITESimplifier::updateQueue(CareMap& queue,
                               TNode e,
                               ITESimplifier::CareSetPtr& careSet)
{
  CareMap::iterator it = queue.find(e), iend = queue.end();
  if (it != iend) {
    set<Node>& cs2 = (*it).second.getCareSet();
    ITESimplifier::CareSetPtr csNew = getNewSet();
    set_intersection(careSet.getCareSet().begin(),
                     careSet.getCareSet().end(),
                     cs2.begin(), cs2.end(),
                     inserter(csNew.getCareSet(), csNew.getCareSet().begin()));
    (*it).second = csNew;
  }
  else {
    queue[e] = careSet;
  }
}


Node ITESimplifier::substitute(TNode e, TNodeMap& substTable, TNodeMap& cache)
{
  TNodeMap::iterator it = cache.find(e), iend = cache.end();
  if (it != iend) {
    return it->second;
  }

  // do substitution?
  it = substTable.find(e);
  iend = substTable.end();
  if (it != iend) {
    Node result = substitute(it->second, substTable, cache);
    cache[e] = result;
    return result;
  }

  size_t sz = e.getNumChildren();
  if (sz == 0) {
    cache[e] = e;
    return e;
  }

  NodeBuilder<> builder(e.getKind());
  if (e.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << e.getOperator();
  }
  for (unsigned i = 0; i < e.getNumChildren(); ++ i) {
    builder << substitute(e[i], substTable, cache);
  }

  Node result = builder;
  // it = substTable.find(result);
  // if (it != iend) {
  //   result = substitute(it->second, substTable, cache);
  // }
  cache[e] = result;
  return result;
}


Node ITESimplifier::simplifyWithCare(TNode e)
{
  TNodeMap substTable;
  CareMap queue;
  CareMap::iterator it;
  ITESimplifier::CareSetPtr cs = getNewSet();
  ITESimplifier::CareSetPtr cs2;
  queue[e] = cs;

  TNode v;
  bool done;
  unsigned i;

  while (!queue.empty()) {
    it = queue.end();
    --it;
    v = it->first;
    cs = it->second;
    set<Node>& css = cs.getCareSet();
    queue.erase(v);

    done = false;
    set<Node>::iterator iCare, iCareEnd = css.end();

    switch (v.getKind()) {
      case kind::ITE: {
        iCare = css.find(v[0]);
        if (iCare != iCareEnd) {
          Assert(substTable.find(v) == substTable.end());
          substTable[v] = v[1];
          updateQueue(queue, v[1], cs);
          done = true;
          break;
        }
        else {
          iCare = css.find(v[0].negate());
          if (iCare != iCareEnd) {
            Assert(substTable.find(v) == substTable.end());
            substTable[v] = v[2];
            updateQueue(queue, v[2], cs);
            done = true;
            break;
          }
        }
        updateQueue(queue, v[0], cs);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0]);
        updateQueue(queue, v[1], cs2);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0].negate());
        updateQueue(queue, v[2], cs2);
        done = true;
        break;
      }
      case kind::AND: {
        for (i = 0; i < v.getNumChildren(); ++i) {
          iCare = css.find(v[i].negate());
          if (iCare != iCareEnd) {
            Assert(substTable.find(v) == substTable.end());
            substTable[v] = d_false;
            done = true;
            break;
          }
        }
        if (done) break;

        Assert(v.getNumChildren() > 1);
        updateQueue(queue, v[0], cs);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0]);
        for (i = 1; i < v.getNumChildren(); ++i) {
          updateQueue(queue, v[i], cs2);
        }
        done = true;
        break;
      }
      case kind::OR: {
        for (i = 0; i < v.getNumChildren(); ++i) {
          iCare = css.find(v[i]);
          if (iCare != iCareEnd) {
            Assert(substTable.find(v) == substTable.end());
            substTable[v] = d_true;
            done = true;
            break;
          }
        }
        if (done) break;

        Assert(v.getNumChildren() > 1);
        updateQueue(queue, v[0], cs);
        cs2 = getNewSet();
        cs2.getCareSet() = css;
        cs2.getCareSet().insert(v[0].negate());
        for (i = 1; i < v.getNumChildren(); ++i) {
          updateQueue(queue, v[i], cs2);
        }
        done = true;
        break;
      }
      default:
        break;
    }

    if (done) {
      continue;
    }

    for (unsigned i = 0; i < v.getNumChildren(); ++i) {
      updateQueue(queue, v[i], cs);
    }
  }
  while (!d_usedSets.empty()) {
    delete d_usedSets.back();
    d_usedSets.pop_back();
  }

  TNodeMap cache;
  return substitute(e, substTable, cache);
}

