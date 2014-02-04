




// Pass 1: label the ite as (constant) or (+ constant variable)

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H
#define __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H

#include "expr/node.h"
#include <ext/hash_map>
#include <ext/hash_set>

namespace CVC4 {
namespace theory {
class ContainsTermITEVistor;

namespace arith {

class ArithIteUtils {
  ContainsTermITEVistor& d_contains;

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  // cache for reduce vars
  NodeMap d_reduceVar; // if reduceVars[n].isNull(), treat reduceVars[n] == n

  // reduceVars[n] = d_constants[n] + d_varParts[n]
  NodeMap d_constants; // d_constants[n] is a constant ite tree
  NodeMap d_varParts; // d_varParts[n] is a polynomial


  NodeMap d_reduceGcd;
  typedef std::hash_map<Node, Integer, NodeHashFunction> NodeIntegerMap;
  NodeIntegerMap d_gcds;

  Integer d_one;

public:
  ArithIteUtils(ContainsTermITEVistor& contains);

  //(ite ?v_2 ?v_1 (ite ?v_3 (- ?v_1 128) (- ?v_1 256)))

  /* applies this to all children of n and constructs the result */
  Node applyReduceVariablesInItes(Node n);

  /** removes common sums variables sums from term ites. */
  Node reduceVariablesInItes(Node n);

  Node reduceConstantIteByGCD(Node n);

  void clear();
private:
  const Integer& gcdIte(Node n);
  Node reduceIteConstantIteByGCD_rec(Node n, const Rational& q);
  Node reduceIteConstantIteByGCD(Node n);
}; /* class ArithIteUtils */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H */
