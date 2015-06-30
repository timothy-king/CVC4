#pragma once

#include <iostream>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {

void produceGuardedQuery(std::ostream& os, const std::vector<Node>& assertions);

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
