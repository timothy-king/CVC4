
#include "cvc4_private.h"

#pragma once

#include <vector>
#include "expr/node.h"

namespace CVC4{
namespace util {

class NaryBuilder {
public:
  static Node mkAssoc(Kind k, const std::vector<Node>& children);
  static Node zeroArity(Kind k);
};/* class RemoveTTE */

}/* util namespace */
}/* CVC4 namespace */
