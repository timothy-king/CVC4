#include "theory/arith/tableau_sizes.h"
#include "theory/arith/matrix.h"

namespace CVC4 {
namespace theory {
namespace arith {

uint32_t TableauSizes::getRowLength(ArithVar b) const {
  RowIndex ridx = d_tab->basicToRowIndex(b);
  return d_tab->getRowLength(ridx);
}

uint32_t TableauSizes::getColumnLength(ArithVar x) const {
  return d_tab->getColLength(x);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
