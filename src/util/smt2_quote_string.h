/*********************                                                        */
/*! \file smt2_quote_string.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Quotes a string if necessary for smt2.
 **
 ** Quotes a string if necessary for smt2.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL__SMT2_QUOTE_STRING_H
#define __CVC4__UTIL__SMT2_QUOTE_STRING_H

#include <string>

namespace CVC4 {

/**
 * SMT-LIB 2 quoting for symbols
 */
std::string quoteSymbol(const std::string& s);

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__SMT2_QUOTE_STRING_H */
