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
void SmtOptionsHandler::dumpMode(std::string option, std::string optarg) {
#ifdef CVC4_DUMPING
  char* optargPtr = strdup(optarg.c_str());
  char* tokstr = optargPtr;
  char* toksave;
  while((optargPtr = strtok_r(tokstr, ",", &toksave)) != NULL) {
    tokstr = NULL;
    if(!strcmp(optargPtr, "benchmark")) {
    } else if(!strcmp(optargPtr, "declarations")) {
    } else if(!strcmp(optargPtr, "assertions")) {
      Dump.on("assertions:post-everything");
    } else if(!strncmp(optargPtr, "assertions:", 11)) {
      const char* p = optargPtr + 11;
      if(!strncmp(p, "pre-", 4)) {
        p += 4;
      } else if(!strncmp(p, "post-", 5)) {
        p += 5;
      } else {
        throw OptionException(std::string("don't know how to dump `") +
                              optargPtr + "'.  Please consult --dump help.");
      }
      if(!strcmp(p, "everything")) {
      } else if(!strcmp(p, "definition-expansion")) {
      } else if(!strcmp(p, "boolean-terms")) {
      } else if(!strcmp(p, "constrain-subtypes")) {
      } else if(!strcmp(p, "substitution")) {
      } else if(!strcmp(p, "strings-pp")) {
      } else if(!strcmp(p, "skolem-quant")) {
      } else if(!strcmp(p, "simplify")) {
      } else if(!strcmp(p, "static-learning")) {
      } else if(!strcmp(p, "ite-removal")) {
      } else if(!strcmp(p, "repeat-simplify")) {
      } else if(!strcmp(p, "rewrite-apply-to-const")) {
      } else if(!strcmp(p, "theory-preprocessing")) {
      } else if(!strcmp(p, "nonclausal")) {
      } else if(!strcmp(p, "theorypp")) {
      } else if(!strcmp(p, "itesimp")) {
      } else if(!strcmp(p, "unconstrained")) {
      } else if(!strcmp(p, "repeatsimp")) {
      } else {
        throw OptionException(std::string("don't know how to dump `") +
                              optargPtr + "'.  Please consult --dump help.");
      }
      Dump.on("assertions");
    } else if(!strcmp(optargPtr, "skolems")) {
    } else if(!strcmp(optargPtr, "clauses")) {
    } else if(!strcmp(optargPtr, "t-conflicts") ||
              !strcmp(optargPtr, "t-lemmas") ||
              !strcmp(optargPtr, "t-explanations") ||
              !strcmp(optargPtr, "bv-rewrites") ||
              !strcmp(optargPtr, "theory::fullcheck")) {
      // These are "non-state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is dumped, it will interfere with the validity
      // of these generated queries.
      if(Dump.isOn("state")) {
        throw OptionException(std::string("dump option `") + optargPtr +
                              "' conflicts with a previous, "
                              "state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("no-permit-state");
      }
    } else if(!strcmp(optargPtr, "state") ||
              !strcmp(optargPtr, "missed-t-conflicts") ||
              !strcmp(optargPtr, "t-propagations") ||
              !strcmp(optargPtr, "missed-t-propagations")) {
      // These are "state-dumping" modes.  If state (SAT decisions,
      // propagations, etc.) is not dumped, it will interfere with the
      // validity of these generated queries.
      if(Dump.isOn("no-permit-state")) {
        throw OptionException(std::string("dump option `") + optargPtr +
                              "' conflicts with a previous, "
                              "non-state-dumping dump option.  You cannot "
                              "mix stateful and non-stateful dumping modes; "
                              "see --dump help.");
      } else {
        Dump.on("state");
      }
    } else if(!strcmp(optargPtr, "help")) {
      puts(s_dumpHelp.c_str());
      exit(1);
    } else if(!strcmp(optargPtr, "bv-abstraction")) {
      Dump.on("bv-abstraction");
    } else if(!strcmp(optargPtr, "bv-algebraic")) {
      Dump.on("bv-algebraic");
    } else {
      throw OptionException(std::string("unknown option for --dump: `") +
                            optargPtr + "'.  Try --dump help.");
    }

    Dump.on(optargPtr);
    Dump.on("benchmark");
    if(strcmp(optargPtr, "benchmark")) {
      Dump.on("declarations");
      if(strcmp(optargPtr, "declarations")) {
        Dump.on("skolems");
      }
    }
  }
  free(optargPtr);
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}


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
  std::ostream* outStream = NULL;
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --dump-to"));
  } else if(optarg == "-") {
    outStream = &DumpOutC::dump_cout;
  } else if(!options::filesystemAccess()) {
    throw OptionException(std::string("Filesystem access not permitted"));
  } else {
    errno = 0;
    outStream = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(outStream == NULL || !*outStream) {
      std::stringstream ss;
      ss << "Cannot open dump-to file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
  }
  DumpOstreamUpdate dumpGetStream;
  dumpGetStream.apply(outStream);
#else /* CVC4_DUMPING */
  throw OptionException("The dumping feature was disabled in this build of CVC4.");
#endif /* CVC4_DUMPING */
}

void SmtOptionsHandler::setRegularOutputChannel(std::string option, std::string optarg) {
  std::ostream* outStream = NULL;
  if(optarg == "") {
    throw OptionException(std::string("Bad file name setting for regular output channel"));
  } else if(optarg == "stdout") {
    outStream = &std::cout;
  } else if(optarg == "stderr") {
    outStream = &std::cerr;
  } else if(!options::filesystemAccess()) {
    throw OptionException(std::string("Filesystem access not permitted"));
  } else {
    errno = 0;
    outStream = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(outStream == NULL || !*outStream) {
      std::stringstream ss;
      ss << "Cannot open regular-output-channel file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
  }

#warning "TODO: Why was this using options::err instead of options::out?"
  OptionsErrOstreamUpdate optionsErrOstreamUpdate;
  optionsErrOstreamUpdate.apply(outStream);
}

void SmtOptionsHandler::setDiagnosticOutputChannel(std::string option, std::string optarg) {
  std::ostream* outStream = NULL;
  if(optarg == "") {
    throw OptionException(std::string("Bad file name setting for diagnostic output channel"));
  } else if(optarg == "stdout") {
    outStream = &std::cout;
  } else if(optarg == "stderr") {
    outStream = &std::cerr;
  } else if(!options::filesystemAccess()) {
    throw OptionException(std::string("Filesystem access not permitted"));
  } else {
    errno = 0;
    outStream = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(outStream == NULL || !*outStream) {
      std::stringstream ss;
      ss << "Cannot open diagnostic-output-channel file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
  }

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

void SmtOptionsHandler::setPrintSuccess(std::string option, bool value) {
  Debug.getStream() << Command::printsuccess(value);
  Trace.getStream() << Command::printsuccess(value);
  Notice.getStream() << Command::printsuccess(value);
  Chat.getStream() << Command::printsuccess(value);
  Message.getStream() << Command::printsuccess(value);
  Warning.getStream() << Command::printsuccess(value);
  *options::out() << Command::printsuccess(value);
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
