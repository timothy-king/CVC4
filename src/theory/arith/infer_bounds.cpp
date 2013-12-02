#include "theory/arith/infer_bounds.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {

InferBoundsParameters::InferBoundsParameters()
  : d_effort(LookupAndSimplexOnFailure)
  , d_paramKind(NumVars)
  , d_parameter(1)
  , d_upperBound(true)
  , d_threshold()
{}

InferBoundsParameters::~InferBoundsParameters(){}

InferBoundsParameters InferBoundsParameters::mkLookup() {
  return InferBoundsParameters(Lookup, Direct, 0, true);
}
InferBoundsParameters InferBoundsParameters::mkUnbounded(){
  return InferBoundsParameters(TryBoth, Unbounded, 0, true);
}
InferBoundsParameters InferBoundsParameters::mkKRounds(int param){
  return InferBoundsParameters(Simplex, Direct, param, true);
}

InferBoundsParameters::Effort InferBoundsParameters::getEffort() const {
  return d_effort;
}

InferBoundsParameters::SimplexParamKind InferBoundsParameters::getParamKind() const {
  return d_paramKind;
}

int InferBoundsParameters::getSimplexRoundParameter() const {
  return d_parameter;
}

bool InferBoundsParameters::findLowerBound() const {
  return ! findUpperBound();
}

bool InferBoundsParameters::findUpperBound() const {
  return d_upperBound;
}

void InferBoundsParameters::setThreshold(const DeltaRational& th){
  d_threshold = th;
  d_useThreshold = true;
}

bool InferBoundsParameters::useThreshold() const{
  return d_useThreshold;
}

const DeltaRational& InferBoundsParameters::getThreshold() const{
  return d_threshold;
}

InferBoundsParameters::InferBoundsParameters(Effort e, SimplexParamKind k, int p, bool ub)
  : d_effort(e)
  , d_paramKind(k)
  , d_parameter(p)
  , d_upperBound(ub)
  , d_useThreshold(false)
  , d_threshold()
{}


InferBoundsResult::InferBoundsResult()
  : d_foundBound(false)
  , d_budgetExhausted(false)
  , d_boundIsProvenOpt(false)
  , d_inconsistentState(false)
  , d_reachedThreshold(false)
  , d_value(false)
  , d_term(Node::null())
  , d_upperBound(true)
  , d_explanation(Node::null())
{}

InferBoundsResult::InferBoundsResult(Node term, bool ub)
  : d_foundBound(false)
  , d_budgetExhausted(false)
  , d_boundIsProvenOpt(false)
  , d_inconsistentState(false)
  , d_reachedThreshold(false)
  , d_value(false)
  , d_term(term)
  , d_upperBound(ub)
  , d_explanation(Node::null())
{}

bool InferBoundsResult::foundBound() const {
  return d_foundBound;
}
bool InferBoundsResult::boundIsOptimal() const {
  return d_boundIsProvenOpt;
}
bool InferBoundsResult::inconsistentState() const {
  return d_inconsistentState;
}

bool InferBoundsResult::boundIsInteger() const{
  return foundBound() && d_value.isIntegral();
}

bool InferBoundsResult::boundIsRational() const {
  return foundBound() && d_value.infinitesimalIsZero();
}

Integer InferBoundsResult::valueAsInteger() const{
  Assert(boundIsInteger());
  return getValue().floor();
}
const Rational& InferBoundsResult::valueAsRational() const{
  Assert(boundIsRational());
  return getValue().getNoninfinitesimalPart();
}

const DeltaRational& InferBoundsResult::getValue() const{
  return d_value;
}

Node InferBoundsResult::getTerm() const { return d_term; }

Node InferBoundsResult::getLiteral() const{
  const Rational& q = getValue().getNoninfinitesimalPart();
  NodeManager* nm = NodeManager::currentNM();
  Node qnode = nm->mkConst(q);

  Kind k;
  if(d_upperBound){
    // x <= q + c*delta
    Assert(getValue().infinitesimalSgn() <= 0);
    k = boundIsRational() ? kind::LEQ : kind::LT;
  }else{
    // x >= q + c*delta
    Assert(getValue().infinitesimalSgn() >= 0);
    k = boundIsRational() ? kind::GEQ : kind::GT;
  }
  Node atom = nm->mkNode(k, getTerm(), qnode);
  Node lit = Rewriter::rewrite(atom);
  return lit;
}

/* If there is a bound, this is a node that explains the bound. */
Node InferBoundsResult::getExplanation() const{
  return d_explanation;
}


void InferBoundsResult::setBound(const DeltaRational& dr, Node exp){
  d_foundBound = true;
  d_value = dr;
  d_explanation = exp;
}

//bool InferBoundsResult::foundBound() const { return d_foundBound; }
//bool InferBoundsResult::boundIsOptimal() const { return d_boundIsProvenOpt; }
//bool InferBoundsResult::inconsistentState() const { return d_inconsistentState; }

  
void InferBoundsResult::setBudgetExhausted() { d_budgetExhausted = true; }
void InferBoundsResult::setReachedThreshold() { d_reachedThreshold = true; }
void InferBoundsResult::setIsOptimal() { d_boundIsProvenOpt = true; }
void InferBoundsResult::setInconsistent() { d_inconsistentState = true; }

bool InferBoundsResult::thresholdWasReached() const{
  return d_reachedThreshold;
}
bool InferBoundsResult::budgetIsExhausted() const{
  return d_budgetExhausted;
}

std::ostream& operator<<(std::ostream& os, const InferBoundsResult& ibr){
  os << "{InferBoundsResult " << std::endl;
  os << "on " << ibr.getTerm() << ", ";
  if(ibr.findUpperBound()){
    os << "find upper bound, ";
  }else{
    os << "find lower bound, ";
  }
  if(ibr.foundBound()){
    os << "found a bound: ";
    if(ibr.boundIsInteger()){
      os << ibr.valueAsInteger() << "(int), ";
    }else if(ibr.boundIsRational()){
      os << ibr.valueAsRational() << "(rat), ";
    }else{
      os << ibr.getValue() << "(extended), ";
    }

    os << "as term " << ibr.getLiteral() << ", ";
    os << "explanation " << ibr.getExplanation() << ", ";
  }else {
    os << "did not find a bound, ";
  }

  if(ibr.boundIsOptimal()){
    os << "(opt), ";
  }

  if(ibr.inconsistentState()){
    os << "(inconsistent), ";
  }
  if(ibr.budgetIsExhausted()){
    os << "(budget exhausted), ";
  }
  if(ibr.thresholdWasReached()){
    os << "(reached threshold), ";
  }
  os << "}";
  return os;
}


} /* namespace arith */
} /* namespace theory */
} /* namespace CVC4 */
