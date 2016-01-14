/*********************                                                        */
/*! \file options_handler_interface.cpp
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

#include "smt/smt_options_handler.h"

#include <cerrno>
#include <cstring>
#include <ostream>
#include <sstream>
#include <string>

#include "base/configuration.h"
#include "base/configuration_private.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "cvc4autoconfig.h"
#include "expr/expr_iomanip.h"
#include "expr/metakind.h"
#include "expr/node_manager.h"
#include "lib/strtok_r.h"
#include "options/arith_heuristic_pivot_rule.h"
#include "options/arith_propagation_mode.h"
#include "options/arith_unate_lemma_mode.h"
#include "options/base_options.h"
#include "options/boolean_term_conversion_mode.h"
#include "options/bv_bitblast_mode.h"
#include "options/bv_options.h"
#include "options/decision_mode.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/open_ostream.h"
#include "options/option_exception.h"
#include "options/options_handler_interface.h"
#include "options/parser_options.h"
#include "options/printer_modes.h"
#include "options/quantifiers_modes.h"
#include "options/set_language.h"
#include "options/simplification_mode.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "options/theoryof_mode.h"
#include "options/ufss_mode.h"
#include "smt/smt_engine.h"
#include "smt/update_ostream.h"
#include "smt_util/command.h"
#include "smt_util/dump.h"
#include "theory/logic_info.h"
#include "util/resource_manager.h"


#warning "TODO: Make SmtOptionsHandler non-public and refactor driver unified."

namespace CVC4 {
namespace smt {

SmtOptionsHandler::SmtOptionsHandler(Options* options)
    : OptionsHandler(options)
{}

SmtOptionsHandler::~SmtOptionsHandler(){}




// smt/options_handlers.h


// This macro is used for setting :regular-output-channel and :diagnostic-output-channel
// to redirect a stream.  It maintains all attributes set on the stream.
#define __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(__channel_get, __channel_set) \
  { \
    int dagSetting = expr::ExprDag::getDag(__channel_get); \
    size_t exprDepthSetting = expr::ExprSetDepth::getDepth(__channel_get); \
    bool printtypesSetting = expr::ExprPrintTypes::getPrintTypes(__channel_get); \
    OutputLanguage languageSetting = language::SetLanguage::getLanguage(__channel_get); \
    __channel_set; \
    __channel_get << expr::ExprDag(dagSetting);      \
    __channel_get << expr::ExprSetDepth(exprDepthSetting); \
    __channel_get << expr::ExprPrintTypes(printtypesSetting); \
    __channel_get << language::SetLanguage(languageSetting); \
  }

void SmtOptionsHandler::setRegularOutputChannel(std::string option, std::string optarg) {
  OstreamOpener opener("regular-output-channel");
  opener.addSpecialCase("stdout", &std::cout);
  opener.addSpecialCase("stderr", &std::cerr);
  std::pair<bool, std::ostream*> pair = opener.open(optarg);
  std::ostream* outStream = pair.second;
#warning "TODO: Garbage collection memory if pair.first is true."
#warning "TODO: Why was this using options::err instead of options::out?"
  OptionsErrOstreamUpdate optionsErrOstreamUpdate;
  optionsErrOstreamUpdate.apply(outStream);
}

void SmtOptionsHandler::setDiagnosticOutputChannel(std::string option, std::string optarg) {
  OstreamOpener opener("diagnostic-output-channel");
  opener.addSpecialCase("stdout", &std::cout);
  opener.addSpecialCase("stderr", &std::cerr);
  std::pair<bool, std::ostream*> pair = opener.open(optarg);
  std::ostream* outStream = pair.second;

#warning "TODO: Garbage collection memory if pair.first is true."

  DebugOstreamUpdate debugOstreamUpdate;
  debugOstreamUpdate.apply(outStream);
  WarningOstreamUpdate warningOstreamUpdate;
  warningOstreamUpdate.apply(outStream);
  MessageOstreamUpdate messageOstreamUpdate;
  messageOstreamUpdate.apply(outStream);
  NoticeOstreamUpdate noticeOstreamUpdate;
  noticeOstreamUpdate.apply(outStream);
  ChatOstreamUpdate chatOstreamUpdate;
  chatOstreamUpdate.apply(outStream);
  TraceOstreamUpdate traceOstreamUpdate;
  traceOstreamUpdate.apply(outStream);
  OptionsErrOstreamUpdate optionsErrOstreamUpdate;
  optionsErrOstreamUpdate.apply(outStream);
}

#undef __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM


}/* CVC4::smt namespace */
}/* CVC4 namespace */
