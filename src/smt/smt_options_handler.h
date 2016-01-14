/*********************                                                        */
/*! \file options_handler_interface.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interface for custom handlers and predicates options.
 **
 ** Interface for custom handlers and predicates options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SMT__SMT_OPTIONS_HANDLER_H
#define __CVC4__SMT__SMT_OPTIONS_HANDLER_H

#include <ostream>
#include <string>

#include "base/modal_exception.h"
#include "options/arith_heuristic_pivot_rule.h"
#include "options/arith_propagation_mode.h"
#include "options/arith_unate_lemma_mode.h"
#include "options/boolean_term_conversion_mode.h"
#include "options/bv_bitblast_mode.h"
#include "options/decision_mode.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/options_handler_interface.h"
#include "options/printer_modes.h"
#include "options/quantifiers_modes.h"
#include "options/simplification_mode.h"
#include "options/theoryof_mode.h"
#include "options/ufss_mode.h"

namespace CVC4 {
namespace smt {

class CVC4_PUBLIC SmtOptionsHandler : public options::OptionsHandler {
public:
  SmtOptionsHandler(Options* options);
  ~SmtOptionsHandler();

  // smt/options_handlers.h
  virtual void dumpToFile(std::string option, std::string optarg);
  virtual void setRegularOutputChannel(std::string option, std::string optarg);
  virtual void setDiagnosticOutputChannel(std::string option, std::string optarg);

}; /* class SmtOptionsHandler */


}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SMT__SMT_OPTIONS_HANDLER_H */
