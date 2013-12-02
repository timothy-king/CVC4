#pragma once

#include "util/integer.h"
#include "util/rational.h"
#include "expr/node.h"
#include "theory/arith/delta_rational.h"
#include <ostream>

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

  Effort getEffort() const;
  SimplexParamKind getParamKind() const;
  int getSimplexRoundParameter() const;

  bool findLowerBound() const;
  bool findUpperBound() const;

  void setFindUpperBound() { d_upperBound = true; }
  void setFindLowerBound() { d_upperBound = false; }

  void setThreshold(const DeltaRational& th);
  bool useThreshold() const;
  const DeltaRational& getThreshold() const;

private:
  InferBoundsParameters(Effort e, SimplexParamKind k, int p, bool ub);

  Effort d_effort;
  SimplexParamKind d_paramKind;
  int d_parameter;
  /* If true, find an upper bound. If false, find a lower bound.*/ 
  bool d_upperBound;
  bool d_useThreshold;
  DeltaRational d_threshold;
};

class InferBoundsResult {
public:
  InferBoundsResult();
  InferBoundsResult(Node term, bool ub);

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
  void setTerm(Node t){ d_term = t; }

  /* If there is a bound, this is a node that explains the bound. */
  Node getExplanation() const;

  bool budgetIsExhausted() const;
  void setBudgetExhausted();

  bool thresholdWasReached() const;
  void setReachedThreshold();

  bool findUpperBound() const { return d_upperBound; }

  void setFindLowerBound() { d_upperBound = false; }
  void setFindUpperBound() { d_upperBound = true; }
private:
  /* was a bound found */
  bool d_foundBound;

  /* was the budget exhausted */
  bool d_budgetExhausted;

  /* does the bound have to be optimal*/
  bool d_boundIsProvenOpt;

  /* was this started on an inconsistent state. */
  bool d_inconsistentState;

  /* reached the threshold. */
  bool d_reachedThreshold;

  /* the value of the bound */
  DeltaRational d_value;

  /* The input term. */
  Node d_term;

  /* Was the bound found an upper or lower bound.*/
  bool d_upperBound;
  
  /* Explanation of the bound. */
  Node d_explanation;
};

std::ostream& operator<<(std::ostream& os, const InferBoundsResult& ibr);

} /* namespace arith */
} /* namespace theory */
} /* namespace CVC4 */
