#include "cvc4_private.h"

#pragma once

#include "util/rational.h"
#include "util/integer.h"

namespace CVC4 {
namespace theory {
namespace arith {


std::pair<Integer, Integer> rootRem(const Integer& u, unsigned long int n);

/**
 * Assumes q >= 0, n >= 0, and D > 0.
 * Returns (l,u) s.t. if x**n = q, then l <= x <= u and u - l <= D.
 */
std::pair<Rational, Rational> estimateNthRoot(const Rational& q, unsigned long int n, const Rational& D);

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
