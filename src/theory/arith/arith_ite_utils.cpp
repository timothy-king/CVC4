#include "theory/arith/arith_ite_utils.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/arith_utilities.h"
#include "theory/ite_utilities.h"
#include "theory/rewriter.h"
#include <ostream>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

Node ArithIteUtils::applyReduceVariablesInItes(Node n){
  NodeBuilder<> nb(n.getKind());
  if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    nb << (n.getOperator());
  }
  for(Node::iterator it = n.begin(), end = n.end(); it != end; ++it){
    nb << reduceVariablesInItes(*it);
  }
  Node res = nb;
  return res;
}

Node ArithIteUtils::reduceVariablesInItes(Node n){
  using namespace CVC4::kind;
  if(d_reduceVar.find(n) != d_reduceVar.end()){
    Node res = d_reduceVar[n];
    return res.isNull() ? n : res;
  }

  switch(n.getKind()){
  case ITE:{
    Node c = n[0], t = n[1], e = n[2];
    if(n.getType().isReal()){
      Node rc = reduceVariablesInItes(c);
      Node rt = reduceVariablesInItes(t);
      Node re = reduceVariablesInItes(e);

      Node vt = d_varParts[t];
      Node ve = d_varParts[e];
      Node vpite = (vt == ve) ? vt : Node::null();

      if(vpite.isNull()){
        Node rite = rc.iteNode(rt, re);
        // do not apply
        d_reduceVar[n] = rite;
        d_constants[n] = mkRationalNode(Rational(0));
        d_varParts[n] = rite; // treat the ite as a variable
        return rite;
      }else{
        NodeManager* nm = NodeManager::currentNM();
        // cout << "vp" << vpite << endl;
        // cout << "\t" << t << " " << d_constants[t] << endl;
        // cout << "\t" << e << " " << d_constants[e] << endl;
        Node constantite = rc.iteNode(d_constants[t], d_constants[e]);
        Node sum = nm->mkNode(kind::PLUS, vpite, constantite);
        cout << n << endl
             << "\t" << sum << endl;
        d_reduceVar[n] = sum;
        d_constants[n] = constantite;
        d_varParts[n] = vpite;
        return sum;
      }
    }else{ // non-arith ite
      if(!d_contains.containsTermITE(n)){
        // don't bother adding to d_reduceVar
        return n;
      }else{
        Node newIte = applyReduceVariablesInItes(n);
        d_reduceVar[n] = (n == newIte) ? Node::null(): newIte;
        return newIte;
      }
    }
  }break;
  default:
    if(n.getType().isReal() && Polynomial::isMember(n)){
      Node newn = Node::null();
      if(!d_contains.containsTermITE(n)){
        newn = n;
      }else if(n.getNumChildren() > 0){
        newn = applyReduceVariablesInItes(n);
        newn = Rewriter::rewrite(newn);
        Assert(Polynomial::isMember(newn));
      }else{
        newn = n;
      }

      Polynomial p = Polynomial::parsePolynomial(newn);
      if(p.isConstant()){
        d_constants[n] = newn;
        d_varParts[n] = mkRationalNode(Rational(0));
        // don't bother adding to d_reduceVar
        return newn;
      }else if(!p.containsConstant()){
        d_constants[n] = mkRationalNode(Rational(0));
        d_varParts[n] = newn;
        d_reduceVar[n] = p.getNode();
        return p.getNode();
      }else{
        Monomial mc = p.getHead();
        d_constants[n] = mc.getConstant().getNode();
        d_varParts[n] = p.getTail().getNode();
        d_reduceVar[n] = newn;
        return newn;
      }
    }else{
      if(!d_contains.containsTermITE(n)){
        return n;
      }
      if(n.getNumChildren() > 0){
        Node res = applyReduceVariablesInItes(n);
        d_reduceVar[n] = res;
        return res;
      }else{
        return n;
      }
    }
    break;
  }
  Unreachable();
  return Node::null();
}

ArithIteUtils::ArithIteUtils(ContainsTermITEVistor& contains)
  : d_contains(contains)
  , d_one(1)
{}

void ArithIteUtils::clear(){
  d_reduceVar.clear();
  d_constants.clear();
  d_varParts.clear();
}

const Integer& ArithIteUtils::gcdIte(Node n){
  if(d_gcds.find(n) != d_gcds.end()){
    return d_gcds[n];
  }
  if(n.getKind() == kind::CONST_RATIONAL){
    const Rational& q = n.getConst<Rational>();
    if(q.isIntegral()){
      d_gcds[n] = q.getNumerator();
      return d_gcds[n];
    }else{
      return d_one;
    }
  }else if(n.getKind() == kind::ITE && n.getType().isReal()){
    const Integer& tgcd = gcdIte(n[1]);
    if(tgcd.isOne()){
      d_gcds[n] = d_one;
      return d_one;
    }else{
      const Integer& egcd = gcdIte(n[2]);
      Integer ite_gcd = tgcd.gcd(egcd);
      d_gcds[n] = ite_gcd;
      return d_gcds[n];
    }
  }
  return d_one;
}

Node ArithIteUtils::reduceIteConstantIteByGCD_rec(Node n, const Rational& q){
  if(n.isConst()){
    Assert(n.getKind() == kind::CONST_RATIONAL);
    return mkRationalNode(n.getConst<Rational>() * q);
  }else{
    Assert(n.getKind() == kind::ITE);
    Assert(n.getType().isInteger());
    Node rc = reduceConstantIteByGCD(n[0]);
    Node rt = reduceIteConstantIteByGCD_rec(n[1], q);
    Node re = reduceIteConstantIteByGCD_rec(n[2], q);
    return rc.iteNode(rt, re);
  }
}

Node ArithIteUtils::reduceIteConstantIteByGCD(Node n){
  Assert(n.getKind() == kind::ITE);
  Assert(n.getType().isReal());
  const Integer& gcd = gcdIte(n);
  if(gcd.isOne()){
    Node newIte = reduceConstantIteByGCD(n[0]).iteNode(n[1],n[2]);
    d_reduceGcd[n] = newIte;
    return newIte;
  }else if(gcd.isZero()){
    Node zeroNode = mkRationalNode(Rational(0));
    d_reduceGcd[n] = zeroNode;
    return zeroNode;
  }else{
    Rational divBy(Integer(1), gcd);
    Node redite = reduceIteConstantIteByGCD_rec(n, divBy);
    Node gcdNode = mkRationalNode(Rational(gcd));
    Node multIte = NodeManager::currentNM()->mkNode(kind::MULT, gcdNode, redite);
    d_reduceGcd[n] = multIte;
    return multIte;
  }
}

Node ArithIteUtils::reduceConstantIteByGCD(Node n){
  if(d_reduceGcd.find(n) != d_reduceGcd.end()){
    return d_reduceGcd[n];
  }
  if(n.getKind() == kind::ITE && n.getType().isReal()){
    return reduceIteConstantIteByGCD(n);
  }

  if(n.getNumChildren() > 0){
    NodeBuilder<> nb(n.getKind());
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      nb << (n.getOperator());
    }
    bool anychange = false;
    for(Node::iterator it = n.begin(), end = n.end(); it != end; ++it){
      Node child = *it;
      Node redchild = reduceConstantIteByGCD(child);
      anychange = anychange || (child != redchild);
      nb << redchild;
    }
    if(anychange){
      Node res = nb;
      d_reduceGcd[n] = res;
      return res;
    }else{
      d_reduceGcd[n] = n;
      return n;
    }
  }else{
    return n;
  }
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
