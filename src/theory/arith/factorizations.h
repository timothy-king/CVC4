

#include "cvc4_private.h"

#pragma once

#include <map>
#include "util/integer.h"
#include "util/rational.h"
#include "util/statistics_registry.h"
#include "theory/arith/normal_form.h"

namespace CVC4 {
namespace theory {
namespace arith {


enum FactoringResult {
  FactorUnknown,
  FactorComputed,
  AlwaysPositive,
  AlwaysNegative
};


class FactorizationModule {
public:
  FactorizationModule();
  
  /**
   * FactorUnknown : unknown
   * FactorComputed : each out[i] is a root of p*d with d > 0
   * AlwaysPositive : p > 0 is valid.
   * AlwaysNegative : p < 0 is valid.
   */
  FactoringResult factorize(const Polynomial& p, Integer& d, std::vector<Polynomial>& out);

  /** Returns equivalent conditions to (cmpKind \prod factor[i] 0) */
  Node signConditions(Kind cmpKind, const std::vector<Polynomial>& factors);
  
private:
  FactoringResult attemptQuadraticDecomposition(const Polynomial& p, Integer& d, std::vector<Polynomial>& out);

  static void fillInRange(std::map<uint32_t, Polynomial>& vPowers, uint32_t start, uint32_t end, const Polynomial& val);

  Node strictLTCount(bool odd, const std::vector<Polynomial>& factors);
  Node zeroConditions(const std::vector<Polynomial>& factors);
  
  class Statistics {
  public:
    IntStat d_factorizeCalls;
    
    Statistics();
    ~Statistics();
  };
  Statistics d_stats;  
};


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
