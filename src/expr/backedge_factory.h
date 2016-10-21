/*********************                                                        */
/*! \file backedge.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EXPR__BACKEDGE_FACTORY_H
#define __CVC4__EXPR__BACKEDGE_FACTORY_H

#include "expr/backedge.h"
#include "expr/node_value.h"

namespace CVC4 {
namespace expr {

/** Factory class for creating backedges in the expression graph. */
class BackedgeFactory {
 public:
  virtual ~BackedgeFactory() {}

  /**
   * Creates a new backedge for the NodeValue and transfers ownership to the
   * caller. This is given a raw NodeValue* to allow the caller to get a mutable
   * version of the underlying data.
   */
  virtual Backedge* createBackedge(NodeValue* nv) = 0;
}; /* class BackedgeFactory */

} /* CVC4::expr namespace */
} /* CVC4 namespace */

#endif /*__CVC4__EXPR__BACKEDGE_FACTORY_H */
