namespace CVC4 {
namespace theory {
namespace arith {

InferBoundsParameters::InferBoundsParameters()
  : d_effort(LookupAndSimplexOnFailure)
  , d_paramKind(NumVars)
  , d_parameter(1)
  , d_lowerBound(true)
  , d_threshold()
{}

static InferBoundsParameters InferBoundsParameters::mkLookup() {
  return InferBoundsParameters(Lookup, Direct, 0);
}
static InferBoundsParameters InferBoundsParameters::mkUnbounded(){
  return InferBoundsParameters(TryBoth, Unbounded, 0);
}
static InferBoundsParameters InferBoundsParameters::mkKRounds(int param){
  return InferBoundsParameters(Simplex, Direct, param);
}

Effort InferBoundsParameters::getEffort() const {
  return d_effort;
}

SimplexRoundParamKind InferBoundsParameters::getParamKind() const {
  return d_paramKind;
}

int InferBoundsParameters::getParamKind() const {
  return d_parameter;
}

bool InferBoundsParameters::findLowerBound() const {
  return d_lowerBound;
}

bool InferBoundsParameters::findUpperBound() const {
  return !findLowerBound();
}

void InferBoundsParameters::setThreshold(const DeltaRational* th) const{
  if(d_threshold == NULL){
    d_threshold = new DeltaRational();
  }
  if(th == NULL){
    delete d_threshold;
    d_threshold = NULL;
  }else{
    (*d_threshold) = *th;
  }
}

const DeltaRational* InferBoundsParameters::getThreshold() const{
  return d_threshold;
}

InferBoundsParameters::InferBoundsParameters(Effort e, SimplexRoundParamKind k, int p, bool lb)
  : d_effort(e)
  , d_paramKind(k)
  , d_parameter(p)
  , d_lowerBound(lb)
  , d_threshold(NULL)
{}


  
InferBoundsResult::InferBoundsResult()
  : d_foundBound(false)
  , d_budgetExhausted(false)
  , d_boundIsProvenOpt(false)
  , d_inconsistentState(false)
  , d_value(false)
  , d_term(Node::null())
  , d_lowerBound(true)
  , d_explanation(Node::null())
{}

bool InferBoundsResult::foundABound() const {
  return d_found;
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
    // q + c*delta <= x
    Assert(getValue().infinitesimalSgn() >= 0);
    k = boundIsRational() ? kind::LEQ : kind::LT;
  }else{
    // q + c*delta >= x
    Assert(getValue().infinitesimalSgn() <= 0);
    k = boundIsRational() ? kind::GEQ : kind::GT;
  }
  Node atom = nm->mkNode(k, qnode, getTerm());
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

bool InferBoundsResult::foundBound() const { return d_foundBound; }
bool InferBoundsResult::boundIsOptimal() const { return d_boundIsProvenOpt; }
bool InferBoundsResult::inconsistentState() const { return d_inconsistentState; }
  
void InferBoundsResult::setBudgetExhausted() { d_budgetExhausted = true; }
void InferBoundsResult::setReachedThreshold() { d_reachedThreshold = true; }
void InferBoundsResult::setIsOpt() { d_boundIsProvenOpt = true; }

} /* namespace arith */
} /* namespace theory */
} /* namespace CVC4 */
