
#include "theory/arith/factorizations.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

FactorizationModule::FactorizationModule()
  : d_stats()
{}

FactorizationModule::Statistics::Statistics()
  : d_factorizeCalls("theory::arith::factorize::calls", 0)
{
  StatisticsRegistry::registerStat(&d_factorizeCalls);  
}


FactorizationModule::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_factorizeCalls);  
}

void printPolynomialMap(Variable v, const std::map<uint32_t, Polynomial>& m, std::ostream& out){
  out << "{polynomial map:";
  for(std::map<uint32_t, Polynomial>::const_iterator i=m.begin(), iend=m.end(); i!=iend; ++i){
    uint32_t power = i->first;
    const Polynomial& p = i->second;
    if( i != m.begin() ) { out << " + "; }
    out << v.getNode() << "**" << power << "*";
    out << "(" << p.getNode() << ")";
  }
  out << "}" << endl;
}

/**
 * FactorUnknown : unknown
 * FactorComputed : p*d == \product_i (out[i]) with d > 0
 * AlwaysPositive : p > 0 is valid.
 * AlwaysNegative : p < 0 is valid.
 */
FactoringResult FactorizationModule::factorize(const Polynomial& p, Integer& d, std::vector<Polynomial>& out){
  FactoringResult res;
  if(!p.isNonlinear()){ return FactorUnknown; }

  res = attemptFactorizeMonomial(p, d, out);
  if(res != FactorUnknown){ return res; }
  
  res = attemptMonomialGCD(p, d, out);
  if(res != FactorUnknown){ return res; }
  
  res = attemptQuadraticDecomposition(p, d, out);
  if(res != FactorUnknown){ return res; }

  return FactorUnknown;
}


FactoringResult FactorizationModule::attemptFactorizeMonomial(const Polynomial& p, Integer& d, std::vector<Polynomial>& out){
  if(p.isConstant()) { return FactorUnknown; }
  if(!p.isNonlinear()) { return FactorUnknown; }
  if(p.size() != 1) { return  FactorUnknown; }

  d = Integer(1);

  Debug("attemptFactorizeMonomial") << "attemptFactorizeMonomial " << p.getNode() << endl;
  
  Monomial m = p.getHead();
  const VarList& vl = m.getVarList();
  out.push_back(Polynomial::mkPolynomial(m.getConstant()));
  
  for(VarList::iterator i = vl.begin(), iend = vl.end(); i != iend; ++i){
    Variable v = *i;
    out.push_back(Polynomial::mkPolynomial(v));
  }
  return FactorComputed;
}

FactoringResult FactorizationModule::attemptMonomialGCD(const Polynomial& p, Integer& d, std::vector<Polynomial>& out){
  if(p.isConstant()) { return FactorUnknown; }
  if(!p.isNonlinear()) { return FactorUnknown; }

  Debug("attemptMonomialGCD") << "attemptMonomialGCD()" << p.getNode() << endl;

  
  Monomial h = p.getHead();
  Polynomial t = p.getTail();
  VarList common = h.getVarList();

  Debug("attemptMonomialGCD") << "head " << h.getNode() << endl;
  for(Polynomial::iterator i = t.begin(), iend = t.end(); !common.empty() && i != iend; ++i){
    Monomial curr = *i;
    Debug("attemptMonomialGCD") << "curr " << curr.getNode() << endl;
    common = common.commonVariables(curr.getVarList());
    Debug("attemptMonomialGCD") << "common " << common.getNode() << endl;
  }
  if(common.empty()) { return FactorUnknown; }
  
  d = Integer(1);
  Polynomial divided = p.exactDivide(common);
  out.push_back(divided);
  out.push_back(Polynomial::mkPolynomial(common));

  Debug("attemptMonomialGCD") << "success "
                              << common.getNode() << " "
                              << divided.getNode() << endl;
  return FactorComputed;
}

FactoringResult FactorizationModule::attemptQuadraticDecomposition(const Polynomial& p, Integer& d, std::vector<Polynomial>& out){
  if(p.isConstant()) { return FactorUnknown; }
  if(!p.isUnivariate()) { return FactorUnknown; }
  if(!p.isNonlinear()) { return FactorUnknown; }

  d = p.denominatorLCM();
  Polynomial ip = p * d;
  
  Assert(ip.isUnivariate());
  Node vAsNode = p.unaryVariable();
  Assert(!vAsNode.isNull());
  Variable v(vAsNode);
  std::map<uint32_t, Polynomial> vPowers = ip.powersOf(v);

  Debug("quadratic") << "quadratic" << vPowers.size() << std::endl;
  if(Debug.isOn("quadratic")){
    printPolynomialMap(v, vPowers, Debug("quadratic"));
  }
  Assert(ip.getNode() == Polynomial::fromPowersOf(v, vPowers).getNode());
  fillInRange(vPowers, 0, 2, Polynomial::mkZero());
  if(Debug.isOn("quadratic")){
    printPolynomialMap(v, vPowers, Debug("quadratic"));
  }
  Assert(ip.getNode() == Polynomial::fromPowersOf(v, vPowers).getNode());
  Assert(vPowers.size() >= 3);
  
  if(vPowers.size() > 3){ return FactorUnknown; }
  
  Assert(vPowers.find(0) != vPowers.end());
  Assert(vPowers.find(1) != vPowers.end());
  Assert(vPowers.find(2) != vPowers.end());

  const Polynomial& a_p = (*(vPowers.find(2))).second;
  const Polynomial& b_p = (*(vPowers.find(1))).second;
  const Polynomial& c_p = (*(vPowers.find(0))).second;

  if(a_p.isZero()){ return FactorUnknown; }
  
  Debug("quadratic") << "a_p:" << a_p.getNode() << endl;
  Debug("quadratic") << "b_p:" << b_p.getNode() << endl;
  Debug("quadratic") << "c_p:" << c_p.getNode() << endl;
  
  Assert(a_p.isConstant());
  Assert(b_p.isConstant());
  Assert(c_p.isConstant());

  const Rational& a_q = a_p.asConstant();
  const Rational& b_q = b_p.asConstant();
  const Rational& c_q = c_p.asConstant();

  Debug("quadratic") << "a_q:" << a_q << endl;
  Debug("quadratic") << "b_q:" << b_q << endl;
  Debug("quadratic") << "c_q:" << c_q << endl;
  
  Assert(a_q.isIntegral());
  Assert(b_q.isIntegral());
  Assert(c_q.isIntegral());
  
  Integer a = a_q.getNumerator();
  Integer b = b_q.getNumerator();
  Integer c = c_q.getNumerator();

  Assert(a.sgn() != 0);
  
  Debug("quadratic") << "a:" << a << endl;
  Debug("quadratic") << "b:" << b << endl;
  Debug("quadratic") << "c:" << c << endl;
  
  Integer discriminant = b*b + (a*c*Integer(-4));

  Debug("quadratic") << "discriminant:" << discriminant << endl;
  if(discriminant.sgn() < 0) {
    // The polynomial is always > 0 or always < 0
    // TODO: improve analysis
    if(c.sgn() > 0){
      Debug("quadratic") << "... AlwaysPositive due to discriminant=" << discriminant << endl;
      return AlwaysPositive;
    } else {
      Assert(c.sgn() < 0);
      Debug("quadratic") << "... AlwaysNegative due to discriminant=" << discriminant << endl;
      return AlwaysNegative;
    }
  }
  Assert(discriminant >= 0);

  Integer sqrt_discriminant;
  bool isPerfect = discriminant.perfectRoot(2, sqrt_discriminant);
  Debug("quadratic") << "(" << discriminant << ").perfectRoot() |-> "
                     << isPerfect << ", " << sqrt_discriminant << endl;
  if(isPerfect){
    // The roots can be respresented in rationals

    Rational sqrt_discriminant_q(sqrt_discriminant);
    Rational one_over_2a(1,a*2);
    Rational neg_b(-b);
    
    Polynomial sqrt_discriminant_p = Polynomial::mkPolynomial(Constant::mkConstant(sqrt_discriminant_q));
    Polynomial minus_b = Polynomial::mkPolynomial(Constant::mkConstant(-b));
    Polynomial plus = (minus_b + sqrt_discriminant_p)*one_over_2a;
    Polynomial minus =(minus_b - sqrt_discriminant_p)*one_over_2a;

    Polynomial f_plus = Polynomial::mkPolynomial(v) - plus;
    Polynomial f_minus = Polynomial::mkPolynomial(v) - minus;

    Assert((a_p*f_plus*f_minus).getNode() == ip.getNode());
    out.push_back(a_p*f_plus);
    out.push_back(f_minus);
    
    Debug("quadratic") << "... FactorComputed" << endl;
    return FactorComputed;
  }

  Debug("quadratic") << "... FactorUnknown due to imperfect root" << endl;
  // The roots cannot be respresented in rationals
  return FactorUnknown;
}

void FactorizationModule::fillInRange(std::map<uint32_t, Polynomial>& vPowers,
                                      uint32_t start,
                                      uint32_t end,
                                      const Polynomial& val)
{
  for(uint32_t i = start; i < end; ++i){
    if(vPowers.find(i) == vPowers.end()){
      vPowers.insert(std::make_pair(i,val));
    }
  }
}

Node FactorizationModule::zeroConditions(const std::vector<Polynomial>& factors){
  NodeBuilder<> nb(kind::OR);
  Polynomial zero = Polynomial::mkZero();
  for( std::vector<Polynomial>::const_iterator i=factors.begin(), iend=factors.end(); i!=iend; ++i){
    const Polynomial& curr = *i;
    Comparison cmp = Comparison::mkComparison(kind::EQUAL, curr, zero);
    nb << cmp.getNode();
  }

  return
    nb.getNumChildren() == 0 ?  NodeManager::currentNM()->mkConst<bool>(true):
    nb.getNumChildren() == 1 ?  nb[0]:
    (Node)nb;
}

/**
 * Let count = | { f < 0 | f \in factors} |
 * If  odd, return a node equivalent to count being odd.
 * If !odd, return a node equivalent to count being even.
 */
Node FactorizationModule::strictLTCount(bool odd, const std::vector<Polynomial>& factors){
  Node curr = NodeManager::currentNM()->mkConst<bool>(!odd);
  Polynomial zero = Polynomial::mkZero();

  // The final result R can be expressed using (+) as xor
  // R := !odd (+) {f_1 < 0} (+) ... (+) {f_k < 0}
  // isOdd(count) <-> {f_1 < 0} (+) ... (+) {f_k < 0}
  // R := !odd (+) isOdd(count)
  // if odd == true, R == false (+) isOdd(count) <-> isOdd(count)
  // else, R == true (+) isOdd(count) <-> !isOdd(count)
  for( std::vector<Polynomial>::const_iterator i=factors.begin(), iend=factors.end(); i!=iend; ++i){
    const Polynomial& p = *i;
    Comparison cmp = Comparison::mkComparison(kind::LT, p, zero);
    Node cmpNode = cmp.getNode();
    curr = curr.xorNode(cmpNode);
  }

  return curr;
}

Node FactorizationModule::signConditions(Kind cmpKind, const std::vector<Polynomial>& factors){
  Debug("fac::signConditions") << cmpKind << endl;
  switch(cmpKind){
  case kind::LT:
    {
      Node zero = zeroConditions(factors);
      Node sltc = strictLTCount(true, factors);
      return ((zero).notNode()).andNode(sltc);
    }
  case kind::GT:
    {
      Node zero = zeroConditions(factors);
      Node sgtc = strictLTCount(false, factors);
      return ((zero).notNode()).andNode(sgtc);
    }
  case kind::LEQ:
    return signConditions(kind::GT, factors).notNode();
  case kind::GEQ:
    return signConditions(kind::LT, factors).notNode();
  case kind::EQUAL:
    return zeroConditions(factors);
  case kind::DISTINCT:
    return signConditions(kind::EQUAL, factors).notNode();
  default:
    return Node::null();
  }
  return Node::null();
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
