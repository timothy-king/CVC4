/*********************                                                        */
/*! \file smt_options_template.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Option handling for SmtEngine
 **
 ** Option handling for SmtEngine.
 **/

#include <string>
#include <sstream>

#include "base/output.h"
#include "base/modal_exception.h"
#include "base/option_exception.h"
#include "options/options_handler_interface.h"


${include_all_option_headers}
${option_handler_includes}

#line 31 "${template}"

using namespace std;

namespace CVC4 {
namespace options {

void OptionsHandler::setOption(const std::string& key, const std::string& optionarg)
  throw(OptionException, ModalException) {
  options::OptionsHandler* const handler = this;
  Trace("options") << "SMT setOption(" << key << ", " << optionarg << ")" << endl;

  ${smt_setoption_handlers}

#line 44 "${template}"

  throw UnrecognizedOptionException(key);
}

std::string OptionsHandler::getOption(const std::string& key) const
  throw(OptionException) {
  Trace("options") << "SMT getOption(" << key << ")" << endl;

  ${smt_getoption_handlers}

#line 57 "${template}"

  throw UnrecognizedOptionException(key);
}

}/* options namespace */
}/* CVC4 namespace */
