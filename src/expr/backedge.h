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

#ifndef __CVC4__EXPR__BACKEDGE_H
#define __CVC4__EXPR__BACKEDGE_H

namespace CVC4 {
namespace expr {

/**
 * A back edge in the node graph. This is to allow for exceptional constructs
 * where node constants contain nodes that may contain cycles. This allows the
 * NodeManager to reclaim this memory manually.
 *
 * Implementations are expected to be able to call removeBackedge() until this
 * object is destroyed.
 */
class Backedge {
 public:
  virtual ~Backedge() {}

  /** Removes a back edge. */
  virtual void removeBackedge() = 0;
};

} /* CVC4::expr namespace */
} /* CVC4 namespace */

#endif /*__CVC4__EXPR__BACKEDGE_H */
