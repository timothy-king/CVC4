/*********************                                                        */
/*! \file unsat_core.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of unsat cores
 **
 ** Representation of unsat cores.
 **/

#include "util/unsat_core.h"
#include "expr/command.h"
#include "smt/smt_engine_scope.h"
#include "printer/printer.h"

namespace CVC4 {

UnsatCore::const_iterator UnsatCore::begin() const {
  return d_core.begin();
}

UnsatCore::const_iterator UnsatCore::end() const {
  return d_core.end();
}

void UnsatCore::toStream(std::ostream& out) const {
  for(UnsatCore::const_iterator i = begin(); i != end(); ++i) {
    out << AssertCommand(*i) << std::endl;
  }
}

std::ostream& operator<<(std::ostream& out, const UnsatCore& core) {
  smt::SmtScope smts(core.d_smt);
  Expr::dag::Scope scope(out, false);
  Printer::getPrinter(options::outputLanguage())->toStream(out, core);
  return out;
}

}/* CVC4 namespace */