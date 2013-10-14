/*********************                                                        */
/*! \file arith_rewriter.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/theory.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"

#include <vector>
#include <set>
#include <stack>

namespace CVC4 {
namespace theory {
namespace arith {

bool ArithRewriter::isAtom(TNode n) {
  Kind k = n.getKind();
  return arith::isRelationOperator(k) || k == kind::IS_INTEGER || k == kind::DIVISIBLE;
}

RewriteResponse ArithRewriter::rewriteConstant(TNode t){
  Assert(t.isConst());
  Assert(t.getKind() == kind::CONST_RATIONAL);

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteVariable(TNode t){
  Assert(t.isVar());

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::rewriteMinus(TNode t, bool pre){
  Assert(t.getKind()== kind::MINUS);

  if(pre){
    if(t[0] == t[1]){
      Rational zero(0);
      Node zeroNode  = mkRationalNode(zero);
      return RewriteResponse(REWRITE_DONE, zeroNode);
    }else{
      Node noMinus = makeSubtractionNode(t[0],t[1]);
      return RewriteResponse(REWRITE_DONE, noMinus);
    }
  }else{
    Polynomial minuend = Polynomial::parsePolynomial(t[0]);
    Polynomial subtrahend = Polynomial::parsePolynomial(t[1]);
    Polynomial diff = minuend - subtrahend;
    return RewriteResponse(REWRITE_DONE, diff.getNode());
  }
}

RewriteResponse ArithRewriter::rewriteUMinus(TNode t, bool pre){
  Assert(t.getKind()== kind::UMINUS);

  if(t[0].getKind() == kind::CONST_RATIONAL){
    Rational neg = -(t[0].getConst<Rational>());
    return RewriteResponse(REWRITE_DONE, mkRationalNode(neg));
  }

  Node noUminus = makeUnaryMinusNode(t[0]);
  if(pre)
    return RewriteResponse(REWRITE_DONE, noUminus);
  else
    return RewriteResponse(REWRITE_AGAIN, noUminus);
}


RewriteResponse ArithRewriter::rewriteDivModTotalNext(TNode t, bool pre){
  Assert(t.getKind()== kind::INTS_DIVISION_TOTAL || t.getKind()== kind::INTS_MODULUS_TOTAL);

  bool isDiv = t.getKind()== kind::INTS_DIVISION_TOTAL;

  TNode num = t[0];
  TNode denom = t[1];

  if(denom.getKind() == kind::CONST_RATIONAL){
    Assert(denom.getConst<Rational>().isIntegral());
    Integer d = denom.getConst<Rational>().getNumerator();
    int origSgn = d.sgn();
    bool negate = false;
    if(origSgn == 0){
      // (div_total x 0) :-> 0
      // (mod_total x 0) :-> 0
      return RewriteResponse(REWRITE_DONE, denom);
    }else if(origSgn < 0){
      // (div_total x (- d)) :-> -(div_total x d)
      // (mod_total x (- d)) :-> (mod_total x d)
      negate = isDiv;
      d = -d;
    }
    Assert(d.sgn() > 0);

    if(num.getKind() == kind::CONST_RATIONAL){
      // (div_total n d) and d != 0 :-> euclidDiv(n,d)
      // (mod_total n d) and d != 0 :-> euclidMod(n,d)
      const Rational& numerator = num.getConst<Rational>();
      Assert(numerator.isIntegral());

      Integer n = numerator.getNumerator();
      Integer res = isDiv ? n.euclidianDivideQuotient(d) : n.euclidianDivideRemainder(d);
      if(negate){
        res = -res;
      }
      Node resNode = mkRationalNode(Rational(res));
      return RewriteResponse(REWRITE_DONE, resNode);
    }
    // num is not a constant

    if(d.isOne()){
      if(isDiv){
        return RewriteResponse(REWRITE_AGAIN, conditionallyNegate(num, negate));
      }else{
        return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
      }
    }
    // d is an integer constant > 1
    if(Polynomial::isMember(num)){
      Polynomial p = Polynomial::parsePolynomial(num);
      if(p.containsConstant()){
        // move a constant in a sum out of the sum

        Constant constant = p.getHead().getConstant();
        Node tail = p.getTail().getNode();

        const Rational& constantValue = constant.getValue();
        Assert(constantValue.isIntegral());
        Assert(!constantValue.isZero());
        Integer c = constantValue.getNumerator();

        Node sum = moveConstantOutOfIntDivMod(tail, c, d, isDiv);
        Node res = conditionallyNegate(sum, negate);
        Debug("nextrewriter") << "nextrewriter " << t << std::endl;
        Debug("nextrewriter") << "-> " << res << std::endl;
        return RewriteResponse(REWRITE_AGAIN_FULL, res);
      }
    }
    if(origSgn < 0){
      NodeManager* nm = NodeManager::currentNM();
      Node dNode = mkRationalNode(Rational(d));
      Node divMod = nm->mkNode(t.getKind(), num, dNode);
      if(negate){
        Node neg = conditionallyNegate(divMod, true);
        return RewriteResponse(REWRITE_AGAIN, neg);
      }else{
        return RewriteResponse(REWRITE_DONE, divMod);
      }
    }
  }
  // fall back case
  return RewriteResponse(REWRITE_DONE, t);
}

// This represents (op (+ t c) d) where op is either div_total or mod_total
// where di >= 2 and ni != 0.
Node ArithRewriter::moveConstantOutOfIntDivMod(Node t, const Integer& c, const Integer& d, bool div){
  Assert(!c.isZero());
  Assert(d.sgn() > 0 && !d.isOne());

  // From smt lib
  // (for all ((m Int) (n Int))
  //   (=> (distinct n 0)
  //       (let ((q (div m n)) (r (mod m n)))
  //         (and (= m (+ (* n q) r))
  //              (<= 0 r (- (abs n) 1))))))
  // d > 1
  // q = (div_tot (+ t c) d)
  // r = (mod_tot (+ t c) d)
  // t + c = d * q + r
  // 0 <= r < d
  // q and r are unique
  //
  // q' = (div_tot t d), r' = (mod_tot t d)
  // t = d * q' + r'
  // 0 <= r' < d
  //
  // t + c = d * q' + r' + c
  //
  // d > 0, euclidean div <=> floor div
  // e = euclidQuot(c,d), f = euclidRem(c,d), 0 <= f < d
  // c = d * e + f
  // t + c = d * (q' + e) + (r' + f)
  // if (r' + f) < d
  //   0 <= (r' + f) < d
  //   t + c = d * (q' + e) + (r' + f)
  //   By uniqueness of solutions:
  //   q = (q' + e), r = (r' + f)
  // else
  //   0 <= (q' + f - d) < d
  //   t + c = d * (e + q' + 1) + (r' + f - d)
  //   q = (q' + e + 1), r = (r' + f - d)
  //
  // (r' + f) < d iff r' < d - f
  // q = q' + e + (ite (r' < d - f) 0 1)
  // r = r' + f + (-d) * (ite (r' < d - f) 0 1)

  Node dNode = mkRationalNode(Rational(d));

  NodeManager* nm = NodeManager::currentNM();
  Node t_mod_denom = nm->mkNode(kind::INTS_MODULUS_TOTAL, t, dNode);

  Integer e,f;
  Integer::euclidianQR(e, f, c, d);

  // (r' < d - f)
  Node zero = mkRationalNode(0);

  // if f is 0, there is a specialization, but do this in atom instead
  Rational diff = Rational(d - f);
  Node lt = nm->mkNode(kind::LT, t_mod_denom, mkRationalNode(diff));
  Node cnd = lt.iteNode(zero, mkRationalNode(1));

  if(div){
    Node t_div_denom = nm->mkNode(kind::INTS_DIVISION_TOTAL, t, dNode);
    Node eNode = mkRationalNode(Rational(e));
    Node sum = nm->mkNode(kind::PLUS, eNode, t_div_denom, cnd);
    return sum;
  }else{
    Node fNode = mkRationalNode(Rational(f));
    Node cndMult = nm->mkNode(kind::MULT, mkRationalNode(-d), cnd);
    Node sum = nm->mkNode(kind::PLUS, fNode, t_mod_denom, cndMult);
    return sum;
  }
}

RewriteResponse ArithRewriter::preRewriteTerm(TNode t){
  if(t.isConst()){
    return rewriteConstant(t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else{
    switch(Kind k = t.getKind()){
    case kind::MINUS:
      return rewriteMinus(t, true);
    case kind::UMINUS:
      return rewriteUMinus(t, true);
    case kind::DIVISION:
    case kind::DIVISION_TOTAL:
      return rewriteDiv(t,true);
    case kind::PLUS:
      return preRewritePlus(t);
    case kind::MULT:
      return preRewriteMult(t);
    case kind::INTS_DIVISION:
    case kind::INTS_MODULUS:
      return RewriteResponse(REWRITE_DONE, t);
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL:
      return rewriteIntsDivModTotal(t,true);
    case kind::ABS:
      if(t[0].isConst()) {
        const Rational& rat = t[0].getConst<Rational>();
        if(rat >= 0) {
          return RewriteResponse(REWRITE_DONE, t[0]);
        } else {
          return RewriteResponse(REWRITE_DONE,
                                 NodeManager::currentNM()->mkConst(-rat));
        }
      }
      return RewriteResponse(REWRITE_DONE, t);
    case kind::IS_INTEGER:
    case kind::TO_INTEGER:
      return RewriteResponse(REWRITE_DONE, t);
    case kind::TO_REAL:
      return RewriteResponse(REWRITE_DONE, t[0]);
    default:
      Unhandled(k);
    }
  }
}
RewriteResponse ArithRewriter::postRewriteTerm(TNode t){
  if(t.isConst()){
    return rewriteConstant(t);
  }else if(t.isVar()){
    return rewriteVariable(t);
  }else{
    switch(t.getKind()){
    case kind::MINUS:
      return rewriteMinus(t, false);
    case kind::UMINUS:
      return rewriteUMinus(t, false);
    case kind::DIVISION:
    case kind::DIVISION_TOTAL:
      return rewriteDiv(t, false);
    case kind::PLUS:
      return postRewritePlus(t);
    case kind::MULT:
      return postRewriteMult(t);
    case kind::INTS_DIVISION:
    case kind::INTS_MODULUS:
      return RewriteResponse(REWRITE_DONE, t);
    case kind::INTS_DIVISION_TOTAL:
    case kind::INTS_MODULUS_TOTAL:
      return rewriteIntsDivModTotal(t, false);
    case kind::ABS:
      if(t[0].isConst()) {
        const Rational& rat = t[0].getConst<Rational>();
        if(rat >= 0) {
          return RewriteResponse(REWRITE_DONE, t[0]);
        } else {
          return RewriteResponse(REWRITE_DONE,
                                 NodeManager::currentNM()->mkConst(-rat));
        }
      }
    case kind::TO_REAL:
      return RewriteResponse(REWRITE_DONE, t[0]);
    case kind::TO_INTEGER:
      if(t[0].isConst()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(Rational(t[0].getConst<Rational>().floor())));
      }
      if(t[0].getType().isInteger()) {
        return RewriteResponse(REWRITE_DONE, t[0]);
      }
      //Unimplemented("TO_INTEGER, nonconstant");
      //return rewriteToInteger(t);
      return RewriteResponse(REWRITE_DONE, t);
    case kind::IS_INTEGER:
      if(t[0].isConst()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(t[0].getConst<Rational>().getDenominator() == 1));
      }
      if(t[0].getType().isInteger()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
      //Unimplemented("IS_INTEGER, nonconstant");
      //return rewriteIsInteger(t);
      return RewriteResponse(REWRITE_DONE, t);
    default:
      Unreachable();
    }
  }
}


RewriteResponse ArithRewriter::preRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT);

  // Rewrite multiplications with a 0 argument and to 0
  Rational qZero(0);

  for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
    if((*i).getKind() == kind::CONST_RATIONAL) {
      if((*i).getConst<Rational>() == qZero) {
        return RewriteResponse(REWRITE_DONE, mkRationalNode(qZero));
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, t);
}
RewriteResponse ArithRewriter::preRewritePlus(TNode t){
  Assert(t.getKind()== kind::PLUS);

  return RewriteResponse(REWRITE_DONE, t);
}

RewriteResponse ArithRewriter::postRewritePlus(TNode t){
  Assert(t.getKind()== kind::PLUS);

  Polynomial res = Polynomial::mkZero();

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    Node curr = *i;
    Polynomial currPoly = Polynomial::parsePolynomial(curr);

    res = res + currPoly;
  }

  return RewriteResponse(REWRITE_DONE, res.getNode());
}

RewriteResponse ArithRewriter::postRewriteMult(TNode t){
  Assert(t.getKind()== kind::MULT);

  Polynomial res = Polynomial::mkOne();

  for(TNode::iterator i = t.begin(), end = t.end(); i != end; ++i){
    Node curr = *i;
    Polynomial currPoly = Polynomial::parsePolynomial(curr);

    res = res * currPoly;
  }

  return RewriteResponse(REWRITE_DONE, res.getNode());
}

RewriteResponse ArithRewriter::postRewriteAtom(TNode atom){
  if(atom.getKind() == kind::IS_INTEGER) {
    if(atom[0].isConst()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(atom[0].getConst<Rational>().isIntegral()));
    }
    if(atom[0].getType().isInteger()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
    }
    // not supported, but this isn't the right place to complain
    return RewriteResponse(REWRITE_DONE, atom);
  } else if(atom.getKind() == kind::DIVISIBLE) {
    if(atom[0].isConst()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(bool((atom[0].getConst<Rational>() / atom.getOperator().getConst<Divisible>().k).isIntegral())));
    }
    if(atom.getOperator().getConst<Divisible>().k.isOne()) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
    }
    return RewriteResponse(REWRITE_AGAIN, NodeManager::currentNM()->mkNode(kind::EQUAL, NodeManager::currentNM()->mkNode(kind::INTS_MODULUS_TOTAL, atom[0], NodeManager::currentNM()->mkConst(Rational(atom.getOperator().getConst<Divisible>().k))), NodeManager::currentNM()->mkConst(Rational(0))));
  }

  // left |><| right
  TNode left = atom[0];
  TNode right = atom[1];

  Polynomial pleft = Polynomial::parsePolynomial(left);
  Polynomial pright = Polynomial::parsePolynomial(right);

  Comparison cmp = Comparison::mkComparison(atom.getKind(), pleft, pright);
  Assert(cmp.isNormalForm());
  return RewriteResponse(REWRITE_DONE, cmp.getNode());
}

RewriteResponse ArithRewriter::preRewriteAtom(TNode atom){
  Assert(isAtom(atom));

  NodeManager* currNM = NodeManager::currentNM();

  if(atom.getKind() == kind::EQUAL) {
    if(atom[0] == atom[1]) {
      return RewriteResponse(REWRITE_DONE, currNM->mkConst(true));
    }
  }else if(atom.getKind() == kind::GT){
    Node leq = currNM->mkNode(kind::LEQ, atom[0], atom[1]);
    return RewriteResponse(REWRITE_DONE, currNM->mkNode(kind::NOT, leq));
  }else if(atom.getKind() == kind::LT){
    Node geq = currNM->mkNode(kind::GEQ, atom[0], atom[1]);
    return RewriteResponse(REWRITE_DONE, currNM->mkNode(kind::NOT, geq));
  }else if(atom.getKind() == kind::IS_INTEGER){
    if(atom[0].getType().isInteger()){
      return RewriteResponse(REWRITE_DONE, currNM->mkConst(true));
    }
  }else if(atom.getKind() == kind::DIVISIBLE){
    if(atom.getOperator().getConst<Divisible>().k.isOne()){
      return RewriteResponse(REWRITE_DONE, currNM->mkConst(true));
    }
  }

  return RewriteResponse(REWRITE_DONE, atom);
}

RewriteResponse ArithRewriter::postRewrite(TNode t){
  if(isTerm(t)){
    RewriteResponse response = postRewriteTerm(t);
    if(Debug.isOn("arith::rewriter") && response.status == REWRITE_DONE) {
      Polynomial::parsePolynomial(response.node);
    }
    return response;
  }else if(isAtom(t)){
    RewriteResponse response = postRewriteAtom(t);
    if(Debug.isOn("arith::rewriter") && response.status == REWRITE_DONE) {
      Comparison::parseNormalForm(response.node);
    }
    return response;
  }else{
    Unreachable();
    return RewriteResponse(REWRITE_DONE, Node::null());
  }
}

RewriteResponse ArithRewriter::preRewrite(TNode t){
  if(isTerm(t)){
    return preRewriteTerm(t);
  }else if(isAtom(t)){
    return preRewriteAtom(t);
  }else{
    Unreachable();
    return RewriteResponse(REWRITE_DONE, Node::null());
  }
}

Node ArithRewriter::makeUnaryMinusNode(TNode n){
  Rational qNegOne(-1);
  return NodeManager::currentNM()->mkNode(kind::MULT, mkRationalNode(qNegOne),n);
}

Node ArithRewriter::makeSubtractionNode(TNode l, TNode r){
  Node negR = makeUnaryMinusNode(r);
  Node diff = NodeManager::currentNM()->mkNode(kind::PLUS, l, negR);

  return diff;
}

RewriteResponse ArithRewriter::rewriteDiv(TNode t, bool pre){
  Assert(t.getKind() == kind::DIVISION_TOTAL || t.getKind()== kind::DIVISION);


  Node left = t[0];
  Node right = t[1];
  if(right.getKind() == kind::CONST_RATIONAL){
    const Rational& den = right.getConst<Rational>();

    if(den.isZero()){
      if(t.getKind() == kind::DIVISION_TOTAL){
        return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
      }else{
        // This is unsupported, but this is not a good place to complain
        return RewriteResponse(REWRITE_DONE, t);
      }
    }
    Assert(den != Rational(0));

    if(left.getKind() == kind::CONST_RATIONAL){
      const Rational& num = left.getConst<Rational>();
      Rational div = num / den;
      Node result =  mkRationalNode(div);
      return RewriteResponse(REWRITE_DONE, result);
    }

    Rational div = den.inverse();

    Node result = mkRationalNode(div);

    Node mult = NodeManager::currentNM()->mkNode(kind::MULT,left,result);
    if(pre){
      return RewriteResponse(REWRITE_DONE, mult);
    }else{
      return RewriteResponse(REWRITE_AGAIN, mult);
    }
  }else{
    return RewriteResponse(REWRITE_DONE, t);
  }
}

RewriteResponse ArithRewriter::rewriteIntsDivModTotal(TNode t, bool pre){
  Kind k = t.getKind();
  // Assert(k == kind::INTS_MODULUS || k == kind::INTS_MODULUS_TOTAL ||
  //        k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);

  //Leaving the function as before (INTS_MODULUS can be handled),
  // but restricting its use here
  Assert(k == kind::INTS_MODULUS_TOTAL || k == kind::INTS_DIVISION_TOTAL);

  if(k == kind::INTS_MODULUS_TOTAL || k == kind::INTS_DIVISION_TOTAL){
    return rewriteDivModTotalNext(t, pre);
  }

  TNode n = t[0], d = t[1];
  bool dIsConstant = d.getKind() == kind::CONST_RATIONAL;
  if(dIsConstant && d.getConst<Rational>().isZero()){
    if(k == kind::INTS_MODULUS_TOTAL || k == kind::INTS_DIVISION_TOTAL){
      return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
    }else{
      // Do nothing for k == INTS_MODULUS
      return RewriteResponse(REWRITE_DONE, t);
    }
  }else if(dIsConstant && d.getConst<Rational>().isOne()){
    if(k == kind::INTS_MODULUS || k == kind::INTS_MODULUS_TOTAL){
      return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
    }else{
      Assert(k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);
      return RewriteResponse(REWRITE_AGAIN, n);
    }
  }else if(dIsConstant && d.getConst<Rational>().isNegativeOne()){
    if(k == kind::INTS_MODULUS || k == kind::INTS_MODULUS_TOTAL){
      return RewriteResponse(REWRITE_DONE, mkRationalNode(0));
    }else{
      Assert(k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);
      return RewriteResponse(REWRITE_AGAIN, NodeManager::currentNM()->mkNode(kind::UMINUS, n));
    }
  }else if(dIsConstant && n.getKind() == kind::CONST_RATIONAL){
    Assert(d.getConst<Rational>().isIntegral());
    Assert(n.getConst<Rational>().isIntegral());
    Assert(!d.getConst<Rational>().isZero());
    Integer di = d.getConst<Rational>().getNumerator();
    Integer ni = n.getConst<Rational>().getNumerator();

    bool isDiv = (k == kind::INTS_DIVISION || k == kind::INTS_DIVISION_TOTAL);

    Integer result = isDiv ? ni.euclidianDivideQuotient(di) : ni.euclidianDivideRemainder(di);

    Node resultNode = mkRationalNode(Rational(result));
    return RewriteResponse(REWRITE_DONE, resultNode);
  }else{
    return RewriteResponse(REWRITE_DONE, t);
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
