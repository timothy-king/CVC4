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

class ChannelSettings {
 public:
  ChannelSettings(std::ostream& out)
      : d_dagSetting(expr::ExprDag::getDag(out)),
        d_exprDepthSetting(expr::ExprSetDepth::getDepth(out)),
        d_printtypesSetting(expr::ExprPrintTypes::getPrintTypes(out)),
        d_languageSetting(language::SetLanguage::getLanguage(out))
  {}

  void apply(std::ostream& out) {
    out << expr::ExprDag(d_dagSetting);
    out << expr::ExprSetDepth(d_exprDepthSetting);
    out << expr::ExprPrintTypes(d_printtypesSetting);
    out << language::SetLanguage(d_languageSetting);
  }

 private:
  const int d_dagSetting;
  const size_t d_exprDepthSetting;
  const bool d_printtypesSetting;
  const OutputLanguage d_languageSetting;
};

class OstreamUpdate {
public:
  virtual std::ostream& get() = 0;
  virtual void set(std::ostream* setTo) = 0;

  void apply(std::ostream* setTo) {
    PrettyCheckArgument(setTo != NULL, setTo);

    ChannelSettings initialSettings(get());
    set(setTo);
    initialSettings.apply(get());
  }
}; /* class OstreamReferenceLambda */

class OptionsErrOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return *(options::err()); }
  virtual void set(std::ostream* setTo) { return options::err.set(setTo); }
};  /* class OptionsErrOstreamUpdate */

class DumpOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return Dump.getStream(); }
  virtual void set(std::ostream* setTo) { Dump.setStream(*setTo); }
};  /* class DumpOstreamUpdate */

class DebugOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return Debug.getStream(); }
  virtual void set(std::ostream* setTo) { Debug.setStream(*setTo); }
};  /* class DebugOstreamUpdate */

class WarningOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return Warning.getStream(); }
  virtual void set(std::ostream* setTo) { Warning.setStream(*setTo); }
};  /* class WarningOstreamUpdate */

class MessageOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return Message.getStream(); }
  virtual void set(std::ostream* setTo) { Message.setStream(*setTo); }
};  /* class MessageOstreamUpdate */

class NoticeOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return Notice.getStream(); }
  virtual void set(std::ostream* setTo) { Notice.setStream(*setTo); }
};  /* class NoticeOstreamUpdate */

class ChatOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return Chat.getStream(); }
  virtual void set(std::ostream* setTo) { Chat.setStream(*setTo); }
};  /* class ChatOstreamUpdate */

class TraceOstreamUpdate : public OstreamUpdate {
 public:
  virtual std::ostream& get() { return Trace.getStream(); }
  virtual void set(std::ostream* setTo) { Trace.setStream(*setTo); }
};  /* class TraceOstreamUpdate */

void SmtOptionsHandler::dumpToFile(std::string option, std::string optarg) {
#ifdef CVC4_DUMPING
  OstreamOpener opener("dump-to");
  opener.addSpecialCase("-", &DumpOutC::dump_cout);
  std::pair<bool, std::ostream*> pair = opener.open(optarg);
  std::ostream* outStream = pair.second;

  DumpOstreamUpdate dumpGetStream;
  dumpGetStream.apply(outStream);
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
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


/* options/base_options_handlers.h */


}/* CVC4::smt namespace */
}/* CVC4 namespace */
