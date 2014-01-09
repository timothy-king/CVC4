
#include "cvc4_private.h"

#pragma once

#include "util/statistics_registry.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/linear_equality.h"
#include "util/dense_map.h"
#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {

struct PrimitiveVec {
  int len;
  int* inds;
  double* coeffs;
  PrimitiveVec();
  ~PrimitiveVec();
  bool initialized() const;
  void clear();
  void setup(int l);
  void print(std::ostream& out) const;
};

enum CutInfoKlass{ MirCutKlass, GmiCutKlass, UnknownKlass};

class CutInfo {
public:
  CutInfoKlass klass;
  int ord;    /* cut's ordinal in the current node pool */
  //int cut_type;   /* Lowerbound or upperbound. */
  Kind cut_type_;   /* Lowerbound, upperbound or undefined. */
  double cut_rhs; /* right hand side of the cut */
  PrimitiveVec cut_vec; /* vector of the cut */
  int M;     /* the number of rows at the time the cut was made.
             * this is required to descramble indices later*/

  int selected; /* if selected, make this non-zero */

  /* if the cut is successfully reproduced this is non-null */
  Node asLiteral;
  Node explanation;

  CutInfo(CutInfoKlass kl, int ordinal);

  virtual ~CutInfo(){}

  void print(std::ostream& out) const;
  void init_cut(int l);
};

class CutsOnNode{
private:
  int d_nid;
  std::vector<CutInfo*> d_cuts;
  std::map<int, int> d_selected;

  /* keeps the first n cuts in d_cuts. */
  void shrinkCuts(size_t n);

public:
  CutsOnNode();
  CutsOnNode(int node);
  ~CutsOnNode();

  int getNodeId() const;
  void addSelected(int ord, int sel);
  void applySelected();
  void addCut(CutInfo* ci);
  void print(std::ostream& o) const;

  typedef std::vector<CutInfo*>::const_iterator const_iterator;
  const_iterator begin() const { return d_cuts.begin(); }
  const_iterator end() const { return d_cuts.end(); }
};

class TreeLog {
private:
  std::map<int, CutsOnNode> d_toNode;

public:
  TreeLog();
  void addCut(int nid, CutInfo* ci);
  void addSelected(int nid, int ord, int sel);
  void applySelected();
  void print(std::ostream& o) const;

  typedef std::map<int, CutsOnNode>::const_iterator const_iterator;
  const_iterator begin() const { return d_toNode.begin(); }
  const_iterator end() const { return d_toNode.end(); }
};

class ApproximateSimplex{
protected:
  int d_pivotLimit;
  int d_branchLimit;
  TreeLog d_log;

public:

  static bool enabled();

  /**
   * If glpk is enabled, return a subclass that can do something.
   * If glpk is disabled, return a subclass that does nothing.
   */
  static ApproximateSimplex* mkApproximateSimplexSolver(const ArithVariables& vars);
  ApproximateSimplex();
  virtual ~ApproximateSimplex(){}

  /** A result is either sat, unsat or unknown.*/
  enum ApproxResult {ApproxError, ApproxSat, ApproxUnsat};
  struct Solution {
    DenseSet newBasis;
    DenseMap<DeltaRational> newValues;
    Solution() : newBasis(), newValues(){}
  };

  /** Sets a deterministic effort limit. */
  void setPivotLimit(int pivotLimit);

  /** Sets a maximization criteria for the approximate solver.*/
  virtual void setOptCoeffs(const ArithRatPairVec& ref) = 0;

  virtual ArithRatPairVec heuristicOptCoeffs() const = 0;

  virtual ApproxResult solveRelaxation() = 0;
  virtual Solution extractRelaxation() const = 0;

  virtual ApproxResult solveMIP() = 0;
  virtual Solution extractMIP() const = 0;

  /** UTILITIES FOR DEALING WITH ESTIMATES */

  static const double SMALL_FIXED_DELTA;
  static const double TOLERENCE;

  /** Returns true if two doubles are roughly equal based on TOLERENCE and SMALL_FIXED_DELTA.*/
  static bool roughlyEqual(double a, double b);

  /**
   * Estimates a double as a Rational using continued fraction expansion that
   * cuts off the estimate once the value is approximately zero.
   * This is designed for removing rounding artifacts.
   */
  static Rational estimateWithCFE(double d);

  /**
   * Converts a rational to a continued fraction expansion representation
   * using a maximum number of expansions equal to depth as long as the expression
   * is not roughlyEqual() to 0.
   */
  static std::vector<Integer> rationalToCfe(const Rational& q, int depth);

  /** Converts a continued fraction expansion representation to a rational. */
  static Rational cfeToRational(const std::vector<Integer>& exp);

  /** Estimates a rational as a continued fraction expansion.*/
  //static Rational estimateWithCFE(const Rational& q, int depth);
  static Rational estimateWithCFE(const Rational& q, const Integer& K);
};/* class ApproximateSimplex */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
