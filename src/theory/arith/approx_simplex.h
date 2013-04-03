
#include "cvc4_private.h"

#pragma once

#include "util/statistics_registry.h"
#include "theory/arith/linear_equality.h"
#include "util/dense_map.h"

namespace CVC4 {
namespace theory {
namespace arith {


class ApproximateSimplex{
public:
  static const double SMALL_FIXED_DELTA;
  static const double TOLERENCE;

  /**
   * If glpk is enabled, return a subclass that can do something.
   * If glpk is disabled, return a sublass that does nothing.
   */
  static ApproximateSimplex* mkApproximateSimplexSolver(const ArithVariables& vars);
  static bool roughlyEqual(double a, double b);

  virtual ~ApproximateSimplex(){}

  enum ApproxResult {ApproxError, ApproxSat, ApproxUnsat};
  struct Solution {
    DenseSet newBasis;
    DenseMap<DeltaRational> newValues;
    Solution() : newBasis(), newValues(){}
  };

  virtual ApproxResult solveRelaxation(unsigned pivotLimit) {
    return ApproxError;
  }
  virtual Solution extractRelaxation() const {
    return Solution();
  }

  virtual ApproxResult solveMIP(unsigned pivotLimit) {
    return ApproxError;
  }
  virtual Solution extractMIP() const {
    return Solution();
  }

  static void applySolution(LinearEqualityModule& linEq, const Solution& sol){
    linEq.forceNewBasis(sol.newBasis);
    linEq.updateMany(sol.newValues);
  }

};/* class ApproximateSimplex */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
