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


#include "theory/ite_compressor.h"
#include <utility>
#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace std;
using namespace CVC4;
using namespace theory;

// bool ITESimplifier::leavesAreConst(TNode e){
//   return leavesAreConst(e, theory::Theory::theoryOf(e));
// }

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
ITECompressor::ITECompressor() {
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

ITECompressor::~ITECompressor() {
  reset();
}

void ITECompressor::reset(){
  d_reachCount.clear();
  d_compressed.clear();
}

void ITECompressor::garbageCollect(){
  reset();
}

ITECompressor::Statistics::Statistics():
  d_compressCalls("ite-simp::compressCalls", 0),
  d_skolemsAdded("ite-simp::skolems", 0)
{
  StatisticsRegistry::registerStat(&d_compressCalls);
  StatisticsRegistry::registerStat(&d_skolemsAdded);

}
ITECompressor::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_compressCalls);
  StatisticsRegistry::unregisterStat(&d_skolemsAdded);
}

bool ITECompressor::debugContainsTermITE(TNode e){
  bool result = false;
#ifdef CVC4_ASSERTIONS
  if(d_debugContainsTermITECache.find(e) != d_debugContainsTermITECache.end()){
    result = d_debugContainsTermITECache[e];
  }else{
    for(unsigned i =0, N = e.getNumChildren(); !result && i < N; ++i){
      result = debugContainsTermITE(e[i]);
    }
    d_debugContainsTermITECache[e] = result;
  }
#endif
  return result;
}


// static unsigned numBranches = 0;
// static unsigned numFalseBranches = 0;
// static unsigned itesMade = 0;

// Node ITESimplifier::constantIteEqualsConstant(TNode cite, TNode constant){
//   static int instance = 0;
//   ++instance;
//   Debug("ite::constantIteEqualsConstant") << instance << "constantIteEqualsConstant("<<cite << ", " << constant<<")"<< endl;
//   if(cite.isConst()){
//     Node res = (cite == constant) ? d_true : d_false;
//     Debug("ite::constantIteEqualsConstant") << instance << "->" << res << endl;
//     return res;
//   }
//   std::pair<Node,Node> pair = make_pair(cite, constant);

//   NodePairMap::const_iterator eq_pos = d_constantIteEqualsConstantCache.find(pair);
//   if(eq_pos != d_constantIteEqualsConstantCache.end()){
//     Debug("ite::constantIteEqualsConstant") << instance << "->" << (*eq_pos).second << endl;
//     return (*eq_pos).second;
//   }

//   ++d_citeEqConstApplications;

//   NodeVec* leaves = computeConstantLeaves(cite);
//   Assert(leaves != NULL);
//   if(std::binary_search(leaves->begin(), leaves->end(), constant)){
//     if(leaves->size() == 1){
//       // probably unreachable
//       d_constantIteEqualsConstantCache[pair] = d_true;
//       Debug("ite::constantIteEqualsConstant") << instance << "->" << d_true << endl;
//       return d_true;
//     }else{
//       Assert(cite.getKind() == kind::ITE);
//       TNode cnd = cite[0];
//       TNode tB = cite[1];
//       TNode fB = cite[2];
//       Node tEqs = constantIteEqualsConstant(tB, constant);
//       Node fEqs = constantIteEqualsConstant(fB, constant);
//       Node boolIte = cnd.iteNode(tEqs, fEqs);
//       if(!(tEqs.isConst() || fEqs.isConst())){
//         ++numBranches;
//       }
//       if(!(tEqs == d_false || fEqs == d_false)){
//         ++numFalseBranches;
//       }
//       ++itesMade;
//       d_constantIteEqualsConstantCache[pair] = boolIte;
//       //Debug("ite::constantIteEqualsConstant") << instance << "->" << boolIte << endl;
//       return boolIte;
//     }
//   }else{
//     d_constantIteEqualsConstantCache[pair] = d_false;
//     Debug("ite::constantIteEqualsConstant") << instance << "->" << d_false << endl;
//     return d_false;
//   }
// }

// Node ITESimplifier::compressITEIntoConjunct(Node ite){
//   Assert(ite.getKind() == kind::ITE);
//   Assert(ite.getType().isBoolean());
//   Assert(ite[1] == d_false || ite[2] == d_false);

//   NodeBuilder<> conjunctBuilder(kind::AND);

//   Node curr = ite;
//   // (ite c false e) <=> (and (not c) e)
//   // (ite c t false) <=> (and c t)
//   while(curr.getKind() == kind::ITE &&
//         (curr[1] == d_false || curr[2] == d_false)){
//     bool negate = (curr[1] == d_false);
//     if(negate ? (curr[0] == d_true) : (curr[0] == d_false)){
//       return d_false; // short cut falses
//     }
//     Node cnd = negate ? (curr[0]).notNode() : (Node)curr[0];
//     conjunctBuilder << cnd;
//     curr = negate ? curr[2] : curr[1];
//   }
//   Assert(compressing.size() > 0);

//   Assert(conjunctBuilder.getNumChildren() >= 1);
//   Node maybeRecurse =
//     (curr.getKind() == kind::ITE) ? compressITE(curr) : curr;
//   if(maybeRecurse.isConst()){
//     if(maybeRecurse == d_false){
//       return d_false;
//     }else{
//       Assert(maybeRecurse == d_true);
//       // is d_true, don't append
//     }
//   }else{
//     conjunctBuilder << maybeRecurse;
//   }
//   Node conjunct = (conjunctBuilder.getNumChildren() == 1) ?
//     conjunctBuilder[0] : (Node)conjunctBuilder;
//   return conjunct;
// }

// Node ITESimplifier::compressITE(Node ite){
//   return ite;

//   // if(ite.isConst()){
//   //   return ite;
//   // }

//   // NodeMap::const_iterator it = d_compressIteMap.find(ite);
//   // if(it != d_compressIteMap.end()){
//   //   return (*it).second;
//   // }else if(ite.getKind() != kind::ITE){
//   //   d_compressIteMap[ite] =ite;
//   //   return ite;
//   // }else{
//   //   if(ite[0].isConst()){
//   //     Node branch = (ite[0] == d_true) ? ite[1] : ite[2];
//   //     // don't bother to cache!
//   //     return compressITE(branch);
//   //   }
//   //   if(ite[1] == d_false || ite[2] == d_false){
//   //     Node conjunct = compressITEIntoConjunct(ite);
//   //     d_compressIteMap[conjunct] = ite;
//   //     return ite;
//   //   }else{
//   //     Node compressThen = compressITE(ite[1]);
//   //     Node compressElse = compressITE(ite[2]);
//   //     Node newIte = ite[0].iteNode(compressThen, compressElse);
//   //     d_compressIteMap[ite] = newIte;
//   //     d_compressIteMap[newIte] = newIte;
//   //     return newIte;
//   //   }
//   // }
// }

// Node ITESimplifier::intersectConstantIte(TNode lcite, TNode rcite){
//   // intersect the constant ite trees lcite and rcite

//   if(lcite.isConst() || rcite.isConst()){
//     bool lIsConst = lcite.isConst();
//     TNode constant = lIsConst ? lcite : rcite;
//     TNode cite = lIsConst ? rcite : lcite;

//     (d_statistics.d_inSmaller)<< 1;
//     unsigned preItesMade = itesMade;
//     unsigned preNumBranches = numBranches;
//     unsigned preNumFalseBranches = numFalseBranches;
//     Node bterm = constantIteEqualsConstant(cite, constant);
//     Debug("intersectConstantIte")
//       << (numBranches - preNumBranches)
//       << " " << (numFalseBranches - preNumFalseBranches)
//       << " " << (itesMade - preItesMade) << endl;
//     return bterm;
//   }
//   Assert(lcite.getKind() == kind::ITE);
//   Assert(rcite.getKind() == kind::ITE);

//   NodeVec* leftValues = computeConstantLeaves(lcite);
//   NodeVec* rightValues = computeConstantLeaves(rcite);

//   uint32_t smaller = std::min(leftValues->size(), rightValues->size());
//   (d_statistics.d_inSmaller)<< smaller;

//   NodeVec intersection(std::max(leftValues->size(), leftValues->size()));
//   NodeVec::iterator newEnd;
//   newEnd = std::set_intersection(leftValues->begin(), leftValues->end(),
//                                  rightValues->begin(), rightValues->end(),
//                                  intersection.begin());
//   intersection.resize(newEnd - intersection.begin());
//   if(intersection.empty()){
//     return d_false;
//   }else{
//     NodeBuilder<> nb(kind::OR);
//     NodeVec::const_iterator it = intersection.begin(), end=intersection.end();
//     for(; it != end; ++it){
//       Node inBoth = *it;
//       Node lefteq = constantIteEqualsConstant(lcite, inBoth);
//       Node righteq = constantIteEqualsConstant(rcite, inBoth);
//       Node bothHold = lefteq.andNode(righteq);
//       nb << bothHold;
//     }
//     Node result = (nb.getNumChildren() >= 1) ? (Node)nb : nb[0];
//     return result;
//   }
// }


// Node ITESimplifier::attemptEagerRemoval(TNode atom){
//   if(atom.getKind() == kind::EQUAL){
//     TNode left = atom[0];
//     TNode right = atom[1];
//     if((left.isConst() &&
//         right.getKind() == kind::ITE && isConstantIte(right)) ||
//        (right.isConst() &&
//         left.getKind() == kind::ITE && isConstantIte(left))){
//       TNode constant = left.isConst() ? left : right;
//       TNode cite = left.isConst() ? right : left;

//       std::pair<Node,Node> pair = make_pair(cite, constant);
//       NodePairMap::const_iterator eq_pos = d_constantIteEqualsConstantCache.find(pair);
//       if(eq_pos != d_constantIteEqualsConstantCache.end()){
//         Node ret = (*eq_pos).second;
//         if(ret.isConst()){
//           return ret;
//         }else{
//           return Node::null();
//         }
//       }

//       NodeVec* leaves = computeConstantLeaves(cite);
//       Assert(leaves != NULL);
//       if(!std::binary_search(leaves->begin(), leaves->end(), constant)){
//         std::pair<Node,Node> pair = make_pair(cite, constant);
//         d_constantIteEqualsConstantCache[pair] = d_false;
//         return d_false;
//       }
//     }
//   }
//   return Node::null();
// }

// Node ITESimplifier::attemptConstantRemoval(TNode atom){
//   if(atom.getKind() == kind::EQUAL){
//     TNode left = atom[0];
//     TNode right = atom[1];
//     if(isConstantIte(left) && isConstantIte(right)){
//       return intersectConstantIte(left, right);
//     }
//   }
//   return Node::null();
// }


// bool ITESimplifier::leavesAreConst(TNode e, TheoryId tid)
// {
//   Assert((e.getKind() == kind::ITE && !e.getType().isBoolean()) ||
//          Theory::theoryOf(e) != THEORY_BOOL);
//   if (e.isConst()) {
//     return true;
//   }

//   hash_map<Node, bool, NodeHashFunction>::iterator it;
//   it = d_leavesConstCache.find(e);
//   if (it != d_leavesConstCache.end()) {
//     return (*it).second;
//   }

//   if (!containsTermITE(e) && Theory::isLeafOf(e, tid)) {
//     d_leavesConstCache[e] = false;
//     return false;
//   }

//   Assert(e.getNumChildren() > 0);
//   size_t k = 0, sz = e.getNumChildren();

//   if (e.getKind() == kind::ITE) {
//     k = 1;
//   }

//   for (; k < sz; ++k) {
//     if (!leavesAreConst(e[k], tid)) {
//       d_leavesConstCache[e] = false;
//       return false;
//     }
//   }
//   d_leavesConstCache[e] = true;
//   return true;
// }


// Node ITESimplifier::simpConstants(TNode simpContext, TNode iteNode, TNode simpVar)
// {
//   NodePairMap::iterator it;
//   it = d_simpConstCache.find(pair<Node, Node>(simpContext,iteNode));
//   if (it != d_simpConstCache.end()) {
//     return (*it).second;
//   }

//   if (iteNode.getKind() == kind::ITE) {
//     NodeBuilder<> builder(kind::ITE);
//     builder << iteNode[0];
//     unsigned i = 1;
//     for (; i < iteNode.getNumChildren(); ++ i) {
//       Node n = simpConstants(simpContext, iteNode[i], simpVar);
//       if (n.isNull()) {
//         return n;
//       }
//       builder << n;
//     }
//     // Mark the substitution and continue
//     Node result = builder;
//     result = Rewriter::rewrite(result);
//     d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = result;
//     return result;
//   }

//   if (!containsTermITE(iteNode)) {
//     Node n = Rewriter::rewrite(simpContext.substitute(simpVar, iteNode));
//     d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
//     return n;
//   }

//   Node iteNode2;
//   Node simpVar2;
//   d_simpContextCache.clear();
//   Node simpContext2 = createSimpContext(iteNode, iteNode2, simpVar2);
//   if (!simpContext2.isNull()) {
//     Assert(!iteNode2.isNull());
//     simpContext2 = simpContext.substitute(simpVar, simpContext2);
//     Node n = simpConstants(simpContext2, iteNode2, simpVar2);
//     if (n.isNull()) {
//       return n;
//     }
//     d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
//     return n;
//   }
//   return Node();
// }


// Node ITESimplifier::getSimpVar(TypeNode t)
// {
//   std::hash_map<TypeNode, Node, TypeNode::HashFunction>::iterator it;
//   it = d_simpVars.find(t);
//   if (it != d_simpVars.end()) {
//     return (*it).second;
//   }
//   else {
//     Node var = NodeManager::currentNM()->mkSkolem("iteSimp_$$", t, "is a variable resulting from ITE simplification");
//     d_simpVars[t] = var;
//     return var;
//   }
// }


// Node ITESimplifier::createSimpContext(TNode c, Node& iteNode, Node& simpVar)
// {
//   NodeMap::iterator it;
//   it = d_simpContextCache.find(c);
//   if (it != d_simpContextCache.end()) {
//     return (*it).second;
//   }

//   if (!containsTermITE(c)) {
//     d_simpContextCache[c] = c;
//     return c;
//   }

//   if (c.getKind() == kind::ITE && !c.getType().isBoolean()) {
//     // Currently only support one ite node in a simp context
//     // Return Null if more than one is found
//     if (!iteNode.isNull()) {
//       return Node();
//     }
//     simpVar = getSimpVar(c.getType());
//     if (simpVar.isNull()) {
//       return Node();
//     }
//     d_simpContextCache[c] = simpVar;
//     iteNode = c;
//     return simpVar;
//   }

//   NodeBuilder<> builder(c.getKind());
//   if (c.getMetaKind() == kind::metakind::PARAMETERIZED) {
//     builder << c.getOperator();
//   }
//   unsigned i = 0;
//   for (; i < c.getNumChildren(); ++ i) {
//     Node newChild = createSimpContext(c[i], iteNode, simpVar);
//     if (newChild.isNull()) {
//       return newChild;
//     }
//     builder << newChild;
//   }
//   // Mark the substitution and continue
//   Node result = builder;
//   d_simpContextCache[c] = result;
//   return result;
// }
// typedef std::hash_set<Node, NodeHashFunction> NodeSet;
// void countReachable_(Node x, Kind k, NodeSet& visited, uint32_t& reached){
//   if(visited.find(x) != visited.end()){
//     return;
//   }
//   visited.insert(x);
//   if(x.getKind() == k){
//     ++reached;
//   }
//   for(unsigned i =0, N=x.getNumChildren(); i < N; ++i){
//     countReachable_(x[i], k, visited, reached);
//   }
// }

// uint32_t countReachable(TNode x, Kind k){
//   NodeSet visited;
//   uint32_t reached = 0;
//   countReachable_(x, k, visited, reached);
//   return reached;
// }

// Node ITESimplifier::simpITEAtom(TNode atom)
// {
//   static int CVC4_UNUSED instance = 0;
//   Debug("ite::atom") << "still simplifying " << (++instance) << endl;
//   Node attempt = transformAtom(atom);
//   Debug("ite::atom") << "  finished " << instance << endl;
//   if(!attempt.isNull()){
//     Node rewritten = Rewriter::rewrite(attempt);
//     Debug("ite::print-success")
//       << instance << " "
//       << "rewriting " << countReachable(rewritten, kind::ITE)
//       <<  " from " <<  countReachable(atom, kind::ITE) << endl
//       << "\t rewritten " << rewritten << endl
//       << "\t input " << atom << endl;
//     return rewritten;
//   }

//   if (leavesAreConst(atom)) {
//     Node iteNode;
//     Node simpVar;
//     d_simpContextCache.clear();
//     Node simpContext = createSimpContext(atom, iteNode, simpVar);
//     if (!simpContext.isNull()) {
//       if (iteNode.isNull()) {
//         Assert(leavesAreConst(simpContext) && !containsTermITE(simpContext));
//         ++(d_statistics.d_unexpected);
//         Debug("ite::simpite") << instance << " "
//                               << "how about?" << atom << endl;
//         Debug("ite::simpite") << instance << " "
//                               << "\t" << simpContext << endl;
//         return Rewriter::rewrite(simpContext);
//       }
//       Node n = simpConstants(simpContext, iteNode, simpVar);
//       if (!n.isNull()) {
//         ++(d_statistics.d_unexpected);
//         Debug("ite::simpite") << instance << " "
//                               << "here?" << atom << endl;
//         Debug("ite::simpite") << instance << " "
//                               << "\t" << n << endl;
//         return n;
//       }
//     }
//   }
//   if(Debug.isOn("ite::simpite")){
//     if(countReachable(atom, kind::ITE) > 0){
//       Debug("ite::simpite") << instance << " "
//                             << "remaining " << atom << endl;
//     }
//   }
//   ++(d_statistics.d_unsimplified);
//   return atom;
// }


// struct preprocess_stack_element {
//   TNode node;
//   bool children_added;
//   preprocess_stack_element(TNode node)
//   : node(node), children_added(false) {}
// };/* struct preprocess_stack_element */


// Node ITESimplifier::simpITE(TNode assertion)
// {
//   // Do a topological sort of the subexpressions and substitute them
//   vector<preprocess_stack_element> toVisit;
//   toVisit.push_back(assertion);

//   static int call = 0;
//   ++call;
//   int iteration = 0;

//   while (!toVisit.empty())
//   {
//     iteration ++;
//     //cout << "call  " << call << " : " << iteration << endl;
//     // The current node we are processing
//     preprocess_stack_element& stackHead = toVisit.back();
//     TNode current = stackHead.node;

//     // If node has no ITE's or already in the cache we're done, pop from the stack
//     if (current.getNumChildren() == 0 ||
//         (Theory::theoryOf(current) != THEORY_BOOL && !containsTermITE(current))) {
//        d_simpITECache[current] = current;
//        ++(d_statistics.d_simpITEVisits);
//        toVisit.pop_back();
//        continue;
//     }

//     NodeMap::iterator find = d_simpITECache.find(current);
//     if (find != d_simpITECache.end()) {
//       toVisit.pop_back();
//       continue;
//     }

//     // Not yet substituted, so process
//     if (stackHead.children_added) {
//       // Children have been processed, so substitute
//       NodeBuilder<> builder(current.getKind());
//       if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
//         builder << current.getOperator();
//       }
//       for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
//         Assert(d_simpITECache.find(current[i]) != d_simpITECache.end());
//         Node child = current[i];
//         Node childRes = d_simpITECache[current[i]];
//         builder << childRes;
//       }
//       // Mark the substitution and continue
//       Node result = builder;

//       // If this is an atom, we process it
//       if (Theory::theoryOf(result) != THEORY_BOOL &&
//           result.getType().isBoolean()) {
//         result = simpITEAtom(result);
//       }

//       // if(current != result && result.isConst()){
//       //   static int instance = 0;
//       //   //cout << instance << " " << result << current << endl;
//       // }

//       result = Rewriter::rewrite(result);
//       d_simpITECache[current] = result;
//       ++(d_statistics.d_simpITEVisits);
//       toVisit.pop_back();
//     } else if( false // options::simpCndBeforeBranch()
//                && current.getKind() == kind::ITE) {
//       // TNode cnd = current[0];
//       // TNode tB = current[1];
//       // TNode eB = current[2];
//       // Node simpCnd = simpITE(cnd);

//       // if(simpCnd.isConst()){
//       //   TNode selected = (simpCnd == d_true) ? tB : eB;
//       //   Node simpSelected = simpITE(selected);
//       //   d_simpITECache[current] = simpSelected;
//       //   ++(d_statistics.d_simpITEVisits);
//       //   toVisit.pop_back();
//       // }else{
//       //   stackHead.children_added = true;
//       //   NodeMap::iterator childFind = d_simpITECache.find(tB);
//       //   if (childFind == d_simpITECache.end()) {
//       //     toVisit.push_back(tB);
//       //   }
//       //   childFind = d_simpITECache.find(eB);
//       //   if (childFind == d_simpITECache.end()) {
//       //     toVisit.push_back(eB);
//       //   }
//       // }
//     } else {
//       // if(false //options::simpAtomsEarly() &&
//       //    && (Theory::theoryOf(current) != THEORY_BOOL &&
//       //     current.getType().isBoolean())) {
//       //   Node attempt = attemptEagerRemoval(current);
//       //   if(!attempt.isNull() && attempt.isConst()){
//       //     static int workedcount = 0;
//       //     ++workedcount;
//       //     if(workedcount % 200 == 0){
//       //       Chat() << "worked " << workedcount << endl;
//       //     }
//       //     Node moreSimp = (attempt.isConst()) ? attempt : simpITE(attempt);
//       //     d_simpITECache[current] = moreSimp;
//       //     ++(d_statistics.d_simpITEVisits);
//       //     toVisit.pop_back();
//       //     continue;
//       //   }
//       // }
//       // Mark that we have added the children if any
//       if (current.getNumChildren() > 0) {
//         stackHead.children_added = true;
//         // We need to add the children
//         for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
//           TNode childNode = *child_it;
//           NodeMap::iterator childFind = d_simpITECache.find(childNode);
//           if (childFind == d_simpITECache.end()) {
//             toVisit.push_back(childNode);
//           }
//         }
//       } else {
//         // No children, so we're done
//         d_simpITECache[current] = current;
//         ++(d_statistics.d_simpITEVisits);
//         toVisit.pop_back();
//       }
//     }
//   }
//   return d_simpITECache[assertion];
// }


bool isTheoryAtom(TNode a){
  using namespace kind;
  switch(a.getKind()){
  case EQUAL:
  case DISTINCT:
    return !(a[0].getType().isBoolean());

  case CONST_BOOLEAN:
  case NOT:
  case AND:
  case IFF:
  case IMPLIES:
  case OR:
  case XOR:
  case ITE:
    return false;

  /* from uf */
  case APPLY_UF:
    return a.getType().isBoolean();
  case CARDINALITY_CONSTRAINT:
  case DIVISIBLE:
  case LT:
  case LEQ:
  case GT:
  case GEQ:
  case IS_INTEGER:
  case BITVECTOR_COMP:
  case BITVECTOR_ULT:
  case BITVECTOR_ULE:
  case BITVECTOR_UGT:
  case BITVECTOR_UGE:
  case BITVECTOR_SLT:
  case BITVECTOR_SLE:
  case BITVECTOR_SGT:
  case BITVECTOR_SGE:
    return true;
  default:
    return false;
  }
}

void ITECompressor::computeReachability(const std::vector<Node>& assertions){
  std::vector<TNode> stack(assertions.begin(), assertions.end());

  while(!stack.empty()){
    TNode back = stack.back();
    stack.pop_back();

    switch(back.getMetaKind()){
    case kind::metakind::CONSTANT:
    case kind::metakind::VARIABLE:
      continue;
    default:
      if(d_reachCount.find(back) != d_reachCount.end()){
        d_reachCount[back] = 1 + d_reachCount[back];
        continue;
      }else{
        d_reachCount[back] = 1;
        for(TNode::iterator cit=back.begin(), end = back.end(); cit != end; ++cit){
          stack.push_back(*cit);
        }
      }
    }
  }
}

Node ITECompressor::push_back_boolean(Node original, Node compressed){
  Node rewritten = Rewriter::rewrite(compressed);
  // There is a bug if the rewritter takes a pure boolean expression
  // and changes its theory
  if(rewritten.isConst()){
    d_compressed[compressed] = rewritten;
    d_compressed[original] = rewritten;
    d_compressed[rewritten] = rewritten;
    return rewritten;
  }else if(d_compressed.find(rewritten) != d_compressed.end()){
    Node res = d_compressed[rewritten];
    d_compressed[original] = res;
    d_compressed[compressed] = res;
    return res;
  }else if(rewritten.isVar() ||
           (rewritten.getKind() == kind::NOT && rewritten[0].isVar())){
    d_compressed[original] = rewritten;
    d_compressed[compressed] = rewritten;
    d_compressed[rewritten] = rewritten;
    return rewritten;
  }else{
    NodeManager* nm = NodeManager::currentNM();
    Node skolem = nm->mkSkolem("compress_$$", nm->booleanType());
    d_compressed[rewritten] = skolem;
    d_compressed[original] = skolem;
    d_compressed[compressed] = skolem;

    Node iff = skolem.iffNode(rewritten);
    d_assertions->push_back(iff);
    ++(d_statistics.d_skolemsAdded);
    return skolem;
  }
}

bool ITECompressor::multipleParents(TNode c){
  NodeCountMap::const_iterator it = d_reachCount.find(c);
  return (*it).second >= 2;
}

Node ITECompressor::compressBooleanITEs(Node toCompress){
  Assert(toCompress.getKind() == kind::ITE);
  Assert(toCompress.getType().isBoolean());

  if(!(toCompress[1] == d_false || toCompress[2] == d_false)){
    Node cmpCnd = compressBoolean(toCompress[0]);
    if(cmpCnd.isConst()){
      Node branch = (cmpCnd == d_true) ? toCompress[1] : toCompress[2];
      Node res = compressBoolean(branch);
      d_compressed[toCompress] = res;
      return res;
    }else{
      Node cmpThen = compressBoolean(toCompress[1]);
      Node cmpElse = compressBoolean(toCompress[2]);
      Node newIte = cmpCnd.iteNode(cmpThen, cmpElse);
      if(multipleParents(toCompress)){
        return push_back_boolean(toCompress, newIte);
      }else{
        return newIte;
      }
    }
  }

  NodeBuilder<> nb(kind::AND);
  Node curr = toCompress;
  while(curr.getKind() == kind::ITE &&
        (curr[1] == d_false || curr[2] == d_false) &&
        (!multipleParents(curr) || curr == toCompress)){

    bool negateCnd = (curr[1] == d_false);
    Node compressCnd = compressBoolean(curr[0]);
    if(compressCnd.isConst()){
      if(compressCnd.getConst<bool>() == negateCnd){
        return push_back_boolean(toCompress, d_false);
      }else{
        // equivalent to true don't push back
      }
    }else{
      Node pb = negateCnd ? compressCnd.notNode() : compressCnd;
      nb << pb;
    }
    curr = negateCnd ? curr[2] : curr[1];
  }
  Assert(toCompress != curr);

  nb << compressBoolean(curr);
  Node res = nb.getNumChildren() == 1 ? nb[0] : (Node)nb;
  return push_back_boolean(toCompress, res);
}

Node ITECompressor::compressTerm(Node toCompress){
  if(toCompress.isConst() || toCompress.isVar()){
    return toCompress;
  }

  if(d_compressed.find(toCompress) != d_compressed.end()){
    return d_compressed[toCompress];
  }
  if(toCompress.getKind() == kind::ITE){
    Node cmpCnd = compressBoolean(toCompress[0]);
    if(cmpCnd.isConst()){
      Node branch = (cmpCnd == d_true) ? toCompress[1] : toCompress[2];
      Node res = compressTerm(toCompress);
      d_compressed[toCompress] = res;
      return res;
    }else{
      Node cmpThen = compressTerm(toCompress[1]);
      Node cmpElse = compressTerm(toCompress[2]);
      Node newIte = cmpCnd.iteNode(cmpThen, cmpElse);
      d_compressed[toCompress] = newIte;
      return newIte;
    }
  }

  NodeBuilder<> nb(toCompress.getKind());

  if(toCompress.getMetaKind() == kind::metakind::PARAMETERIZED) {
    nb << (toCompress.getOperator());
  }
  for(Node::iterator it = toCompress.begin(), end = toCompress.end(); it != end; ++it){
    nb << compressTerm(*it);
  }
  Node compressed = (Node)nb;
  if(multipleParents(toCompress)){
    d_compressed[toCompress] = compressed;
  }
  return compressed;
}

Node ITECompressor::compressBoolean(Node toCompress){
  static int instance = 0;
  ++instance;
  if(toCompress.isConst() || toCompress.isVar()){
    return toCompress;
  }
  if(d_compressed.find(toCompress) != d_compressed.end()){
    return d_compressed[toCompress];
  }else if(toCompress.getKind() == kind::ITE){
    return compressBooleanITEs(toCompress);
  }else{
    bool ta = isTheoryAtom(toCompress);
    NodeBuilder<> nb(toCompress.getKind());
    if(toCompress.getMetaKind() == kind::metakind::PARAMETERIZED) {
      nb << (toCompress.getOperator());
    }
    for(Node::iterator it = toCompress.begin(), end = toCompress.end(); it != end; ++it){
      Node pb = (ta) ? compressTerm(*it) : compressBoolean(*it);
      nb << pb;
    }
    Node compressed = nb;
    if(ta || multipleParents(toCompress)){
      return push_back_boolean(toCompress, compressed);
    }else{
      return compressed;
    }
  }
}



bool ITECompressor::compress(std::vector<Node>& assertions){
  reset();

  d_assertions = &assertions;
  computeReachability(assertions);

  ++(d_statistics.d_compressCalls);
  Chat() << "Computed reachability" << endl;

  bool nofalses = true;
  size_t original_size = assertions.size();
  Chat () << "compressing " << original_size << endl;
  for(size_t i = 0; i < original_size && nofalses; ++i){
    Node assertion = assertions[i];
    Node compressed =  compressBoolean(assertion);
    Node rewritten = Rewriter::rewrite(compressed);
    assertions[i] = rewritten;
    Assert(!debugContainsTermITE(rewritten));

    nofalses = (rewritten != d_false);
  }

  d_assertions = NULL;

  return nofalses;
}

