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
#include "util/configuration.h"
#include "util/configuration_private.h"
#include "util/resource_manager.h"


#warning "TODO: Make SmtOptionsHandler non-public and refactor driver unified."

namespace CVC4 {
namespace smt {

SmtOptionsHandler::SmtOptionsHandler(Options* options)
    : OptionsHandler(options)
{}

SmtOptionsHandler::~SmtOptionsHandler(){}

// theory/options_handlers.h
void SmtOptionsHandler::useTheory(std::string option, std::string optarg) {
  if(optarg == "help") {
    puts(theory::useTheoryHelp);
    exit(1);
  }
  if(theory::useTheoryValidate(optarg)) {
    std::map<std::string, bool> m = options::theoryAlternates();
    m[optarg] = true;
    options::theoryAlternates.set(m);
  } else {
    throw OptionException(std::string("unknown option for ") + option + ": `" +
                          optarg + "'.  Try --use-theory help.");
  }
}



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
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Dump.getStream(), Dump.setStream(*outStream));
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
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(*options::err(), options::err.set(outStream));
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
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Debug.getStream(), Debug.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Warning.getStream(), Warning.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Message.getStream(), Message.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Notice.getStream(), Notice.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Chat.getStream(), Chat.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(Trace.getStream(), Trace.setStream(*outStream));
  __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(*options::err(), options::err.set(outStream));
}

#undef __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM








// expr/options_handlers.h
void SmtOptionsHandler::setDefaultExprDepth(std::string option, int depth) {
  if(depth < -1) {
    throw OptionException("--default-expr-depth requires a positive argument, or -1.");
  }

  Debug.getStream() << expr::ExprSetDepth(depth);
  Trace.getStream() << expr::ExprSetDepth(depth);
  Notice.getStream() << expr::ExprSetDepth(depth);
  Chat.getStream() << expr::ExprSetDepth(depth);
  Message.getStream() << expr::ExprSetDepth(depth);
  Warning.getStream() << expr::ExprSetDepth(depth);
  // intentionally exclude Dump stream from this list
}

void SmtOptionsHandler::setDefaultDagThresh(std::string option, int dag) {
  if(dag < 0) {
    throw OptionException("--default-dag-thresh requires a nonnegative argument.");
  }

  Debug.getStream() << expr::ExprDag(dag);
  Trace.getStream() << expr::ExprDag(dag);
  Notice.getStream() << expr::ExprDag(dag);
  Chat.getStream() << expr::ExprDag(dag);
  Message.getStream() << expr::ExprDag(dag);
  Warning.getStream() << expr::ExprDag(dag);
  Dump.getStream() << expr::ExprDag(dag);
}

void SmtOptionsHandler::setPrintExprTypes(std::string option) {
  Debug.getStream() << expr::ExprPrintTypes(true);
  Trace.getStream() << expr::ExprPrintTypes(true);
  Notice.getStream() << expr::ExprPrintTypes(true);
  Chat.getStream() << expr::ExprPrintTypes(true);
  Message.getStream() << expr::ExprPrintTypes(true);
  Warning.getStream() << expr::ExprPrintTypes(true);
  // intentionally exclude Dump stream from this list
}


// main/options_handlers.h
void SmtOptionsHandler::showConfiguration(std::string option) {
  fputs(Configuration::about().c_str(), stdout);
  printf("\n");
  printf("version    : %s\n", Configuration::getVersionString().c_str());
  if(Configuration::isGitBuild()) {
    const char* branchName = Configuration::getGitBranchName();
    if(*branchName == '\0') {
      branchName = "-";
    }
    printf("scm        : git [%s %s%s]\n",
           branchName,
           std::string(Configuration::getGitCommit()).substr(0, 8).c_str(),
           Configuration::hasGitModifications() ?
             " (with modifications)" : "");
  } else if(Configuration::isSubversionBuild()) {
    printf("scm        : svn [%s r%u%s]\n",
           Configuration::getSubversionBranchName(),
           Configuration::getSubversionRevision(),
           Configuration::hasSubversionModifications() ?
             " (with modifications)" : "");
  } else {
    printf("scm        : no\n");
  }
  printf("\n");
  printf("library    : %u.%u.%u\n",
         Configuration::getVersionMajor(),
         Configuration::getVersionMinor(),
         Configuration::getVersionRelease());
  printf("\n");
  printf("debug code : %s\n", Configuration::isDebugBuild() ? "yes" : "no");
  printf("statistics : %s\n", Configuration::isStatisticsBuild() ? "yes" : "no");
  printf("replay     : %s\n", Configuration::isReplayBuild() ? "yes" : "no");
  printf("tracing    : %s\n", Configuration::isTracingBuild() ? "yes" : "no");
  printf("dumping    : %s\n", Configuration::isDumpingBuild() ? "yes" : "no");
  printf("muzzled    : %s\n", Configuration::isMuzzledBuild() ? "yes" : "no");
  printf("assertions : %s\n", Configuration::isAssertionBuild() ? "yes" : "no");
  printf("proof      : %s\n", Configuration::isProofBuild() ? "yes" : "no");
  printf("coverage   : %s\n", Configuration::isCoverageBuild() ? "yes" : "no");
  printf("profiling  : %s\n", Configuration::isProfilingBuild() ? "yes" : "no");
  printf("competition: %s\n", Configuration::isCompetitionBuild() ? "yes" : "no");
  printf("\n");
  printf("cudd       : %s\n", Configuration::isBuiltWithCudd() ? "yes" : "no");
  printf("cln        : %s\n", Configuration::isBuiltWithCln() ? "yes" : "no");
  printf("gmp        : %s\n", Configuration::isBuiltWithGmp() ? "yes" : "no");
  printf("glpk       : %s\n", Configuration::isBuiltWithGlpk() ? "yes" : "no");
  printf("abc        : %s\n", Configuration::isBuiltWithAbc() ? "yes" : "no");
  printf("readline   : %s\n", Configuration::isBuiltWithReadline() ? "yes" : "no");
  printf("tls        : %s\n", Configuration::isBuiltWithTlsSupport() ? "yes" : "no");
  exit(0);
}

void SmtOptionsHandler::showDebugTags(std::string option) {
  if(Configuration::isDebugBuild() && Configuration::isTracingBuild()) {
    printf("available tags:");
    unsigned ntags = Configuration::getNumDebugTags();
    char const* const* tags = Configuration::getDebugTags();
    for(unsigned i = 0; i < ntags; ++ i) {
      printf(" %s", tags[i]);
    }
    printf("\n");
  } else if(! Configuration::isDebugBuild()) {
    throw OptionException("debug tags not available in non-debug builds");
  } else {
    throw OptionException("debug tags not available in non-tracing builds");
  }
  exit(0);
}

void SmtOptionsHandler::showTraceTags(std::string option) {
  if(Configuration::isTracingBuild()) {
    printf("available tags:");
    unsigned ntags = Configuration::getNumTraceTags();
    char const* const* tags = Configuration::getTraceTags();
    for (unsigned i = 0; i < ntags; ++ i) {
      printf(" %s", tags[i]);
    }
    printf("\n");
  } else {
    throw OptionException("trace tags not available in non-tracing build");
  }
  exit(0);
}


/* options/base_options_handlers.h */
void SmtOptionsHandler::setVerbosity(std::string option, int value) throw(OptionException) {
  if(Configuration::isMuzzledBuild()) {
    DebugChannel.setStream(CVC4::null_os);
    TraceChannel.setStream(CVC4::null_os);
    NoticeChannel.setStream(CVC4::null_os);
    ChatChannel.setStream(CVC4::null_os);
    MessageChannel.setStream(CVC4::null_os);
    WarningChannel.setStream(CVC4::null_os);
  } else {
    if(value < 2) {
      ChatChannel.setStream(CVC4::null_os);
    } else {
      ChatChannel.setStream(std::cout);
    }
    if(value < 1) {
      NoticeChannel.setStream(CVC4::null_os);
    } else {
      NoticeChannel.setStream(std::cout);
    }
    if(value < 0) {
      MessageChannel.setStream(CVC4::null_os);
      WarningChannel.setStream(CVC4::null_os);
    } else {
      MessageChannel.setStream(std::cout);
      WarningChannel.setStream(std::cerr);
    }
  }
}

void SmtOptionsHandler::increaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() + 1);
  setVerbosity(option, options::verbosity());
}

void SmtOptionsHandler::decreaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() - 1);
  setVerbosity(option, options::verbosity());
}


void SmtOptionsHandler::addTraceTag(std::string option, std::string optarg) {
  if(Configuration::isTracingBuild()) {
    if(!Configuration::isTraceTag(optarg.c_str())) {

      if(optarg == "help") {
        printf("available tags:");
        unsigned ntags = Configuration::getNumTraceTags();
        char const* const* tags = Configuration::getTraceTags();
        for(unsigned i = 0; i < ntags; ++ i) {
          printf(" %s", tags[i]);
        }
        printf("\n");
        exit(0);
      }

      throw OptionException(std::string("trace tag ") + optarg +
                            std::string(" not available.") +
                            suggestTags(Configuration::getTraceTags(), optarg) );
    }
  } else {
    throw OptionException("trace tags not available in non-tracing builds");
  }
  Trace.on(optarg);
}

void SmtOptionsHandler::addDebugTag(std::string option, std::string optarg) {
  if(Configuration::isDebugBuild() && Configuration::isTracingBuild()) {
    if(!Configuration::isDebugTag(optarg.c_str()) &&
       !Configuration::isTraceTag(optarg.c_str())) {

      if(optarg == "help") {
        printf("available tags:");
        unsigned ntags = Configuration::getNumDebugTags();
        char const* const* tags = Configuration::getDebugTags();
        for(unsigned i = 0; i < ntags; ++ i) {
          printf(" %s", tags[i]);
        }
        printf("\n");
        exit(0);
      }

      throw OptionException(std::string("debug tag ") + optarg +
                            std::string(" not available.") +
                            suggestTags(Configuration::getDebugTags(), optarg, Configuration::getTraceTags()) );
    }
  } else if(! Configuration::isDebugBuild()) {
    throw OptionException("debug tags not available in non-debug builds");
  } else {
    throw OptionException("debug tags not available in non-tracing builds");
  }
  Debug.on(optarg);
  Trace.on(optarg);
}

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
