
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/arith_utilities.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {


PseudoBooleanProcessor::PseudoBooleanProcessor(context::Context* user_context)
  : d_pbBounds(user_context)
  , d_pbs(user_context, 0)
{}

bool PseudoBooleanProcessor::decomposeAssertion(Node assertion, bool negated){
  if (assertion.getKind() != kind::GEQ){ return false; }
  Assert(assertion.getKind() == kind::GEQ);

  Debug("pbs::rewrites") << "decomposeAssertion" << assertion  << std::endl;

  Node l = assertion[0];
  Node r = assertion[1];

  if( r.getKind() != kind::CONST_RATIONAL ){
    Debug("pbs::rewrites") << "not rhs constant" << assertion  << std::endl;
    return false;
  }
  // don't bother matching on anything other than + on the left hand side
  if( l.getKind() != kind::PLUS){
    Debug("pbs::rewrites") << "not plus" << assertion  << std::endl;
    return false;
  }

  if(!Polynomial::isMember(l)){
    Debug("pbs::rewrites") << "not polynomial" << assertion  << std::endl;
    return false;
  }

  Polynomial p = Polynomial::parsePolynomial(l);
  clear();
  if(negated){
    // (not (>= p r))
    // (< p r)
    // (> (-p) (-r))
    // (>= (-p) (-r +1))
    d_off = (-r.getConst<Rational>());

    if(d_off.constValue().isIntegral()){
      d_off = d_off.constValue() + Rational(1) ;
    }else{
      d_off = Rational(d_off.constValue().ceiling());
    }
  }else{
    // (>= p r)
    d_off = r.getConst<Rational>();
    d_off = Rational(d_off.constValue().ceiling());
  }
  Assert(d_off.constValue().isIntegral());

  int adj = negated ? -1 : 1;
  for(Polynomial::iterator i=p.begin(), end=p.end(); i != end; ++i){
    Monomial m = *i;
    const Rational& coeff = m.getConstant().getValue();
    if(!(coeff.isOne() || coeff.isNegativeOne())){ return false; }
    Assert(coeff.sgn() != 0);

    const VarList& vl = m.getVarList();
    Node v = vl.getNode();

    if(!isPseudoBoolean(v)){ return false; }
    int sgn = adj * coeff.sgn();
    if(sgn > 0){
      d_pos.push_back(v);
    }else{
      d_neg.push_back(v);
    }
  }
  // all of the variables are pseudoboolean
  // with coefficients +/- and the offsetoff
  return true;
}

bool PseudoBooleanProcessor::isPseudoBoolean(Node v) const{
  CDNode2PairMap::const_iterator ci = d_pbBounds.find(v);
  if(ci != d_pbBounds.end()){
    const PairNode& p = (*ci).second;
    return !(p.first).isNull() && !(p.second).isNull();
  }
  return false;
}

void PseudoBooleanProcessor::addGeqZero(Node v, Node exp){
  Assert(isIntVar(v));
  Assert(!exp.isNull());
  CDNode2PairMap::const_iterator ci = d_pbBounds.find(v);

  Debug("pbs::rewrites") << "addGeqZero " << v << std::endl;

  if(ci == d_pbBounds.end()){
    d_pbBounds.insert(v, std::make_pair(exp, Node::null()));
  }else{
    const PairNode& p = (*ci).second;
    if(p.first.isNull()){
      Assert(!p.second.isNull());
      d_pbBounds.insert(v, std::make_pair(exp, p.second));
      Debug("pbs::rewrites") << "add pbs " << v << std::endl;
      Assert(isPseudoBoolean(v));
      d_pbs = d_pbs + 1;
    }
  }
}

void PseudoBooleanProcessor::addLeqOne(Node v, Node exp){
  Assert(isIntVar(v));
  Assert(!exp.isNull());
  Debug("pbs::rewrites") << "addLeqOne " << v << std::endl;
  CDNode2PairMap::const_iterator ci = d_pbBounds.find(v);
  if(ci == d_pbBounds.end()){
    d_pbBounds.insert(v, std::make_pair(Node::null(), exp));
  }else{
    const PairNode& p = (*ci).second;
    if(p.second.isNull()){
      Assert(!p.first.isNull());
      d_pbBounds.insert(v, std::make_pair(p.first, exp));
      Debug("pbs::rewrites") << "add pbs " << v << std::endl;
      Assert(isPseudoBoolean(v));
      d_pbs = d_pbs + 1;
    }
  }
}

void PseudoBooleanProcessor::learnInternal(Node assertion, bool negated, Node orig){
  switch(assertion.getKind()){
  case kind::GEQ:
    // assume assertion is rewritten
    {
      Node l = assertion[0];
      Node r = assertion[1];


      if(r.getKind() == kind::CONST_RATIONAL){
        const Rational& rc = r.getConst<Rational>();
        if(isIntVar(l)){
          if(!negated && rc.isZero()){  // (>= x 0)
            addGeqZero(l, orig);
          }else if(negated && rc.isNegativeOne()){ // (not (<= x -1))
            addGeqZero(l, orig);
          }else if(negated && rc == Rational(2)){
            addLeqOne(l, orig);
          }
        }else if(l.getKind() == kind::MULT && l.getNumChildren() == 2){
          Node c = l[0], v = l[1];
          if(c.getKind() == kind::CONST_RATIONAL && c.getConst<Rational>().isNegativeOne()){
            if(isIntVar(v)){
              if(!negated && rc.isNegativeOne()){ // (>= (* -1 x) -1)
                addLeqOne(v, orig);
              }
            }
          }
        }
      }
    }
    break;
  case kind::NOT:
    learnInternal(assertion[0], !negated, orig);
    break;
  default:
    break; // do nothing
  }
}

void PseudoBooleanProcessor::learn(Node assertion){
  if(assertion.getKind() == kind::AND){
    Node::iterator ci=assertion.begin(), cend = assertion.end();
    for(; ci != cend; ++ci){
      learn(*ci);
    }
  }else{
    learnInternal(assertion, false, assertion);
  }
}

Node PseudoBooleanProcessor::mkGeqOne(Node v){
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(kind::GEQ, v, mkRationalNode(Rational(1)));
}

void PseudoBooleanProcessor::learn(const NodeVec& assertions){
  NodeVec::const_iterator ci, cend;
  ci = assertions.begin(); cend=assertions.end();
  for(; ci != cend; ++ci ){
    Node assert = Rewriter::rewrite(*ci);
    learn(assert);
  }
}


Node PseudoBooleanProcessor::applyGeq(Node geq, bool negated){
  Assert(geq.getKind() == kind::GEQ);
  bool success = decomposeAssertion(geq, negated);
  if(!success){
    Debug("pbs::rewrites") << "failed " << std::endl;
    return negated ? geq.notNode() : geq;
  }
  Assert(d_off.constValue().isIntegral());
  Integer off = d_off.constValue().ceiling();

  // \sum pos >= \sum neg + off

  // for now special case everything we want
  // target easy clauses
  if( d_pos.size() == 1 && d_neg.size() == 1 && off.isZero() ){
    // x >= y
    // |- (y >= 1) => (x >= 1)
    Node x = d_pos.front();
    Node y = d_neg.front();

    Node xGeq1 = mkGeqOne(x);
    Node yGeq1 = mkGeqOne(y);
    return yGeq1.impNode(xGeq1);
  }
  if( d_pos.size() == 0 && d_neg.size() == 2 && off.isNegativeOne()){
    // 0 >= (x + y -1)
    // |- 1 >= x + y
    // |- (or (not (x >= 1)) (not (y >= 1)))
    Node x = d_neg[0];
    Node y = d_neg[1];

    Node xGeq1 = mkGeqOne(x);
    Node yGeq1 = mkGeqOne(y);
    return (xGeq1.notNode()).orNode(yGeq1.notNode());
  }
  if( d_pos.size() == 2 && d_neg.size() == 1 && off.isZero() ){
    // (x + y) >= z
    // |- (z >= 1) => (or (x >= 1) (y >=1 ))
    Node x = d_pos[0];
    Node y = d_pos[1];
    Node z = d_neg[0];

    Node xGeq1 = mkGeqOne(x);
    Node yGeq1 = mkGeqOne(y);
    Node zGeq1 = mkGeqOne(z);
    NodeManager* nm =NodeManager::currentNM();
    return nm->mkNode(kind::OR, zGeq1.notNode(), xGeq1, yGeq1);
  }

  return negated ? geq.notNode() : geq;
}

Node PseudoBooleanProcessor::applyInternal(Node assertion, bool negated){
  switch(assertion.getKind()){
  case kind::GEQ:
    return applyGeq(assertion, negated);
  case kind::NOT:
    return applyInternal(assertion[0], !negated);
    break;
  default:
    break;
  }
  //return assertion;
  return negated ? assertion.notNode() : assertion;
}

Node PseudoBooleanProcessor::applyReplacements(Node assertion){
  Node result = Node::null();

  if(assertion.getKind() == kind::AND){
    NodeBuilder<> nb(kind::AND);
    bool changed = false;
    for(size_t i=0, N=assertion.getNumChildren(); i < N; ++i){
      Node child = assertion[i];
      Node rep = applyReplacements(child);
      nb << rep;
      changed = changed || child != rep;
    }
    if(changed){
      result =  nb;
    }else{
      result = assertion;
    }
  }else{
    result = applyInternal(assertion, false);
  }

  if( result != assertion ){
    result = Rewriter::rewrite(result);
    Debug("pbs::rewrites") << "applyReplacements" <<assertion << "-> " << result << std::endl;
  }
  return result;
}

bool PseudoBooleanProcessor::likelyToHelp() const{
  return d_pbs >= 100;
}

void PseudoBooleanProcessor::applyReplacements(NodeVec& assertions){
  for(size_t i=0, N=assertions.size(); i < N; ++i){
    Node assertion = Rewriter::rewrite(assertions[i]);
    Node res = applyReplacements(assertion);
    assertions[i] = res;
  }
}

void PseudoBooleanProcessor::clear() {
  d_off.clear();
  d_pos.clear();
  d_neg.clear();
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

