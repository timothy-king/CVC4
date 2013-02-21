
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

  /* If enabled, use glpk. Otherwise do nothing. */
  static void approximateRelaxation(LinearEqualityModule& linEq);

  static bool roughlyEqual(double a, double b);

};/* class ApproximateSimplex */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
