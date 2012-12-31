/*********************                                                        */
/*! \file arithvar.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Defines ArithVar which is the internal representation of variables in arithmetic
 **
 ** This defines ArithVar which is the internal representation of variables in
 ** arithmetic. This is a typedef from Index to ArithVar.
 ** This file also provides utilities for ArithVars.
 **/


#include "cvc4_private.h"

#pragma once

#include <vector>
#include "util/index.h"


namespace CVC4 {
namespace theory {
namespace arith {

typedef Index ArithVar;
extern const ArithVar ARITHVAR_SENTINEL;

typedef std::vector<ArithVar> ArithVarVec;

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

