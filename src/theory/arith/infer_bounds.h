#pragma once

namespace CVC4 {
namespace theory {
namespace arith {

class InferBoundsParameters {
public:
  enum Effort {Lookup, Simplex, LookupAndSimplexOnFailure, TryBoth};
  enum SimplexParamKind { Unbounded, NumVars, Direct};

  InferBoundsParameters();
  ~InferBoundsParameters();

  static InferBoundsParameters mkLookup();
  static InferBoundsParameters mkUnbounded();
  static InferBoundsParameters mkKRounds(int param);

  Effort getEffort() const { return d_effort; }
  SimplexParamKind getParamKind() const { return d_paramKind; }
  int getSimplexRoundParameter() const { return d_parameter; }

  bool findLowerBound() const { return findUpperBound(); }
  bool findUpperBound() const { return d_upperBound; }

  void setFindUpperBound() { d_upperBound = true; }
  void setFindLowerBound() { d_upperBound = false; }

  void setThreshold(const DeltaRational& th) const;
  bool useThreshold() const;
  const DeltaRational& getThreshold() const;

private:
  InferBoundsParameters(Effort e, SimplexParamKind k, int p, bool lb);

  Effort d_effort;
  SimplexParamKind d_paramKind;
  int d_parameter;
  /* If true, find an upper bound. If false, find a lower bound.*/ 
  bool d_upperBound;
  DeltaRational d_threshold;
};

class InferBoundsResult {
public:
  InferBoundsResult();
  InferBoundsResult(Node term, bool ub = true);

  void setBound(const DeltaRational& dr, Node exp);
  bool foundBound() const;

  void setIsOptimal();
  bool boundIsOptimal() const;

  void setInconsistent();
  bool inconsistentState() const;

  const DeltaRational& getValue() const;
  bool boundIsRational() const;
  const Rational& valueAsRational() const;
  bool boundIsInteger() const;
  Integer valueAsInteger() const;

  Node getTerm() const;
  Node getLiteral() const;

  /* If there is a bound, this is a node that explains the bound. */
  Node getExplanation() const;

  bool budgetIsExhausted() const;
  void setBudgetExhausted();

  bool thresholdWasReached() const;
  void setReachedThreshold();

private:
  /* was a bound found */
  bool d_foundBound;

  /* was the budget exhausted */
  bool d_budgetExhausted;

  /* does the bound have to be optimal*/
  bool d_boundIsProvenOpt;

  /* was this started on an inconsistent state. */
  bool d_inconsistentState;

  /* the value of the bound */
  DeltaRational d_value;

  /* The input term. */
  Node d_term;

  bool d_upperBound;
  
  /* Explanation of the bound. */
  Node d_explanation;
};

} /* namespace arith */
} /* namespace theory */
} /* namespace CVC4 */
