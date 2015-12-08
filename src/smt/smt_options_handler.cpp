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

#include <ostream>
#include <string>

#include "base/arith_heuristic_pivot_rule.h"
#include "base/arith_propagation_mode.h"
#include "base/arith_unate_lemma_mode.h"
#include "base/bitblast_mode.h"
#include "base/bitblast_mode.h"
#include "base/boolean_term_conversion_mode.h"
#include "base/decision_mode.h"
#include "base/language.h"
#include "base/modal_exception.h"
#include "base/option_exception.h"
#include "base/printer_modes.h"
#include "base/quantifiers_modes.h"
#include "base/simplification_mode.h"
#include "base/theoryof_mode.h"
#include "base/ufss_mode.h"
#include "options/options_handler_interface.h"
#include "smt/smt_engine.h"
#include "smt/smt_options_handler.h"
#include "theory/logic_info.h"

#include "base/output.h"
#include "base/language.h"
#include "expr/command.h"
#include "options/options_handler_interface.h"
#include "base/didyoumean.h"
#include "util/configuration.h"

namespace CVC4 {
namespace smt {

SmtOptionsHandler::SmtOptionsHandler(SmtEngine* smt)
    : d_smtEngine(smt)
{}

SmtOptionsHandler::~SmtOptionsHandler(){}


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

void SmtOptionsHandler::showDebugTags(std::string option) = 0;
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

void SmtOptionsHandler::threadN(std::string option) {
  throw OptionException(option + " is not a real option by itself.  Use e.g. --thread0=\"--random-seed=10 --random-freq=0.02\" --thread1=\"--random-seed=20 --random-freq=0.05\"");
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

OutputLanguage SmtOptionsHandler::stringToOutputLanguage(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::output::LANG_AUTO;
  }

  try {
    return language::toOutputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() + "\nTry --output-language help");
  }

  Unreachable();
}

InputLanguage SmtOptionsHandler::stringToInputLanguage(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "help") {
    options::languageHelp.set(true);
    return language::input::LANG_AUTO;
  }

  try {
    return language::toInputLanguage(optarg);
  } catch(OptionException& oe) {
    throw OptionException("Error in " + option + ": " + oe.getMessage() + "\nTry --language help");
  }

  Unreachable();
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


std::string SmtOptionsHandler::suggestTags(char const* const* validTags, std::string inputTag,
                                           char const* const* additionalTags)
{
  DidYouMean didYouMean;

  const char* opt;
  for(size_t i = 0; (opt = validTags[i]) != NULL; ++i) {
    didYouMean.addWord(validTags[i]);
  }
  if(additionalTags != NULL) {
    for(size_t i = 0; (opt = additionalTags[i]) != NULL; ++i) {
      didYouMean.addWord(additionalTags[i]);
    }
  }

  return  didYouMean.getMatchAsString(inputTag);
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
