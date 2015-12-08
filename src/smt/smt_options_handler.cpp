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
#include <cerrno>
#include <cstring>
#include <sstream>

#include "base/arith_heuristic_pivot_rule.h"
#include "base/arith_propagation_mode.h"
#include "base/arith_unate_lemma_mode.h"
#include "base/bitblast_mode.h"
#include "base/bitblast_mode.h"
#include "base/boolean_term_conversion_mode.h"
#include "base/decision_mode.h"
#include "base/didyoumean.h"
#include "base/language.h"
#include "base/language.h"
#include "base/modal_exception.h"
#include "base/modal_exception.h"
#include "base/option_exception.h"
#include "base/output.h"
#include "base/output.h"
#include "base/printer_modes.h"
#include "base/quantifiers_modes.h"
#include "base/simplification_mode.h"
#include "base/theoryof_mode.h"
#include "base/ufss_mode.h"
#include "cvc4autoconfig.h"
#include "expr/command.h"
#include "expr/node_manager.h"
#include "lib/strtok_r.h"
#include "options/options_handler_interface.h"
#include "options/options_handler_interface.h"
#include "parser/options.h"
#include "smt/options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine.h"
#include "smt/smt_options_handler.h"
#include "theory/logic_info.h"
#include "util/configuration.h"
#include "util/configuration_private.h"
#include "util/dump.h"
#include "util/dump.h"
#include "util/resource_manager.h"

#include "base/theoryof_mode.h"
#include "expr/metakind.h"
#include "base/decision_mode.h"
#include "main/options.h"
#include "decision/options.h"
#include "theory/options.h"

#include "base/bitblast_mode.h"
#include "main/options.h"
#include "theory/bv/options.h"


namespace CVC4 {
namespace smt {

SmtOptionsHandler::SmtOptionsHandler(SmtEngine* smt)
    : d_smtEngine(smt)
{}

SmtOptionsHandler::~SmtOptionsHandler(){}

// theory/bv/options_handlers.h
void SmtOptionsHandler::abcEnabledBuild(std::string option, bool value) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

void SmtOptionsHandler::abcEnabledBuild(std::string option, std::string value) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(!value.empty()) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

const std::string SmtOptionsHandler::s_bitblastingModeHelp = "\
Bit-blasting modes currently supported by the --bitblast option:\n\
\n\
lazy (default)\n\
+ Separate boolean structure and term reasoning betwen the core\n\
  SAT solver and the bv SAT solver\n\
\n\
eager\n\
+ Bitblast eagerly to bv SAT solver\n\
";

theory::bv::BitblastMode SmtOptionsHandler::stringToBitblastMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "lazy") {
    if (!options::bitvectorPropagate.wasSetByUser()) {
      options::bitvectorPropagate.set(true);
    }
    if (!options::bitvectorEqualitySolver.wasSetByUser()) {
      options::bitvectorEqualitySolver.set(true);
    }
    if (!options::bitvectorEqualitySlicer.wasSetByUser()) {
      if (options::incrementalSolving() ||
          options::produceModels()) {
        options::bitvectorEqualitySlicer.set(theory::bv::BITVECTOR_SLICER_OFF);
      } else {
        options::bitvectorEqualitySlicer.set(theory::bv::BITVECTOR_SLICER_AUTO);
      }
    }

    if (!options::bitvectorInequalitySolver.wasSetByUser()) {
      options::bitvectorInequalitySolver.set(true);
    }
    if (!options::bitvectorAlgebraicSolver.wasSetByUser()) {
      options::bitvectorAlgebraicSolver.set(true);
    }
    return theory::bv::BITBLAST_MODE_LAZY;
  } else if(optarg == "eager") {

    if (options::incrementalSolving() &&
        options::incrementalSolving.wasSetByUser()) {
      throw OptionException(std::string("Eager bit-blasting does not currently support incremental mode. \n\
                                         Try --bitblast=lazy"));
    }
    if (!options::bitvectorToBool.wasSetByUser()) {
      options::bitvectorToBool.set(true);
    }

    if (!options::bvAbstraction.wasSetByUser() &&
        !options::skolemizeArguments.wasSetByUser()) {
      options::bvAbstraction.set(true);
      options::skolemizeArguments.set(true);
    }
    return theory::bv::BITBLAST_MODE_EAGER;
  } else if(optarg == "help") {
    puts(s_bitblastingModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bitblast: `") +
                          optarg + "'.  Try --bitblast=help.");
  }
}

const std::string SmtOptionsHandler::s_bvSlicerModeHelp = "\
Bit-vector equality slicer modes supported by the --bv-eq-slicer option:\n\
\n\
auto (default)\n\
+ Turn slicer on if input has only equalities over core symbols\n\
\n\
on\n\
+ Turn slicer on\n\
\n\
off\n\
+ Turn slicer off\n\
";

theory::bv::BvSlicerMode SmtOptionsHandler::stringToBvSlicerMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "auto") {
    return theory::bv::BITVECTOR_SLICER_AUTO;
  } else if(optarg == "on") {
    return theory::bv::BITVECTOR_SLICER_ON;
  } else if(optarg == "off") {
    return theory::bv::BITVECTOR_SLICER_OFF;
  } else if(optarg == "help") {
    puts(s_bitblastingModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --bv-eq-slicer: `") +
                          optarg + "'.  Try --bv-eq-slicer=help.");
  }
}

void SmtOptionsHandler::setBitblastAig(std::string option, bool arg) throw(OptionException) {
  if(arg) {
    if(options::bitblastMode.wasSetByUser()) {
      if(options::bitblastMode() != theory::bv::BITBLAST_MODE_EAGER) {
        throw OptionException("bitblast-aig must be used with eager bitblaster");
      }
    } else {
      theory::bv::BitblastMode mode = stringToBitblastMode("", "eager");
      options::bitblastMode.set(mode);
    }
    if(!options::bitvectorAigSimplifications.wasSetByUser()) {
      options::bitvectorAigSimplifications.set("balance;drw");
    }
  }
}


// theory/booleans/options_handlers.h
const std::string SmtOptionsHandler::s_booleanTermConversionModeHelp = "\
Boolean term conversion modes currently supported by the\n\
--boolean-term-conversion-mode option:\n\
\n\
bitvectors [default]\n\
+ Boolean terms are converted to bitvectors of size 1.\n\
\n\
datatypes\n\
+ Boolean terms are converted to enumerations in the Datatype theory.\n\
\n\
native\n\
+ Boolean terms are converted in a \"natural\" way depending on where they\n\
  are used.  If in a datatype context, they are converted to an enumeration.\n\
  Elsewhere, they are converted to a bitvector of size 1.\n\
";

theory::booleans::BooleanTermConversionMode SmtOptionsHandler::stringToBooleanTermConversionMode(std::string option, std::string optarg) throw(OptionException){
  if(optarg ==  "bitvectors") {
    return theory::booleans::BOOLEAN_TERM_CONVERT_TO_BITVECTORS;
  } else if(optarg ==  "datatypes") {
    return theory::booleans::BOOLEAN_TERM_CONVERT_TO_DATATYPES;
  } else if(optarg ==  "native") {
    return theory::booleans::BOOLEAN_TERM_CONVERT_NATIVE;
  } else if(optarg ==  "help") {
    puts(s_booleanTermConversionModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --boolean-term-conversion-mode: `") +
                          optarg + "'.  Try --boolean-term-conversion-mode help.");
  }
}

// theory/uf/options_handlers.h
const std::string SmtOptionsHandler::s_ufssModeHelp = "\
UF strong solver options currently supported by the --uf-ss option:\n\
\n\
full \n\
+ Default, use uf strong solver to find minimal models for uninterpreted sorts.\n\
\n\
no-minimal \n\
+ Use uf strong solver to shrink model sizes, but do no enforce minimality.\n\
\n\
none \n\
+ Do not use uf strong solver to shrink model sizes. \n\
\n\
";

theory::uf::UfssMode SmtOptionsHandler::stringToUfssMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg ==  "default" || optarg == "full" ) {
    return theory::uf::UF_SS_FULL;
  } else if(optarg == "no-minimal") {
    return theory::uf::UF_SS_NO_MINIMAL;
  } else if(optarg == "none") {
    return theory::uf::UF_SS_NONE;
  } else if(optarg ==  "help") {
    puts(s_ufssModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --uf-ss: `") +
                          optarg + "'.  Try --uf-ss help.");
  }
}



// theory/options_handlers.h
const std::string SmtOptionsHandler::s_theoryOfModeHelp = "\
TheoryOf modes currently supported by the --theoryof-mode option:\n\
\n\
type (default) \n\
+ type variables, constants and equalities by type\n\
\n\
term \n\
+ type variables as uninterpreted, equalities by the parametric theory\n\
";

theory::TheoryOfMode SmtOptionsHandler::stringToTheoryOfMode(std::string option, std::string optarg) {
  if(optarg == "type") {
    return theory::THEORY_OF_TYPE_BASED;
  } else if(optarg == "term") {
    return theory::THEORY_OF_TERM_BASED;
  } else if(optarg == "help") {
    puts(s_theoryOfModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --theoryof-mode: `") +
                          optarg + "'.  Try --theoryof-mode help.");
  }
}

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



// printer/options_handlers.h
const std::string SmtOptionsHandler::s_modelFormatHelp = "\
Model format modes currently supported by the --model-format option:\n\
\n\
default \n\
+ Print model as expressions in the output language format.\n\
\n\
table\n\
+ Print functional expressions over finite domains in a table format.\n\
";

const std::string SmtOptionsHandler::s_instFormatHelp = "\
Inst format modes currently supported by the --model-format option:\n\
\n\
default \n\
+ Print instantiations as a list in the output language format.\n\
\n\
szs\n\
+ Print instantiations as SZS compliant proof.\n\
";

ModelFormatMode SmtOptionsHandler::stringToModelFormatMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "default") {
    return MODEL_FORMAT_MODE_DEFAULT;
  } else if(optarg == "table") {
    return MODEL_FORMAT_MODE_TABLE;
  } else if(optarg == "help") {
    puts(s_modelFormatHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --model-format: `") +
                          optarg + "'.  Try --model-format help.");
  }
}

InstFormatMode SmtOptionsHandler::stringToInstFormatMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "default") {
    return INST_FORMAT_MODE_DEFAULT;
  } else if(optarg == "szs") {
    return INST_FORMAT_MODE_SZS;
  } else if(optarg == "help") {
    puts(s_instFormatHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-format: `") +
                          optarg + "'.  Try --inst-format help.");
  }
}



// decision/options_handlers.h
const std::string SmtOptionsHandler::s_decisionModeHelp = "\
Decision modes currently supported by the --decision option:\n\
\n\
internal (default)\n\
+ Use the internal decision heuristics of the SAT solver\n\
\n\
justification\n\
+ An ATGP-inspired justification heuristic\n\
\n\
justification-stoponly\n\
+ Use the justification heuristic only to stop early, not for decisions\n\
";

decision::DecisionMode SmtOptionsHandler::stringToDecisionMode(std::string option, std::string optarg) throw(OptionException) {
  options::decisionStopOnly.set(false);

  if(optarg == "internal") {
    return decision::DECISION_STRATEGY_INTERNAL;
  } else if(optarg == "justification") {
    return decision::DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "justification-stoponly") {
    options::decisionStopOnly.set(true);
    return decision::DECISION_STRATEGY_JUSTIFICATION;
  } else if(optarg == "help") {
    puts(s_decisionModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --decision: `") +
                          optarg + "'.  Try --decision help.");
  }
}

decision::DecisionWeightInternal SmtOptionsHandler::stringToDecisionWeightInternal(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "off")
    return decision::DECISION_WEIGHT_INTERNAL_OFF;
  else if(optarg == "max")
    return decision::DECISION_WEIGHT_INTERNAL_MAX;
  else if(optarg == "sum")
    return decision::DECISION_WEIGHT_INTERNAL_SUM;
  else if(optarg == "usr1")
    return decision::DECISION_WEIGHT_INTERNAL_USR1;
  else
    throw OptionException(std::string("--decision-weight-internal must be off, max or sum."));
}



// smt/options_handlers.h
const std::string SmtOptionsHandler::SmtOptionsHandler::s_dumpHelp = "\
Dump modes currently supported by the --dump option:\n\
\n\
benchmark\n\
+ Dump the benchmark structure (set-logic, push/pop, queries, etc.), but\n\
  does not include any declarations or assertions.  Implied by all following\n\
  modes.\n\
\n\
declarations\n\
+ Dump user declarations.  Implied by all following modes.\n\
\n\
skolems\n\
+ Dump internally-created skolem variable declarations.  These can\n\
  arise from preprocessing simplifications, existential elimination,\n\
  and a number of other things.  Implied by all following modes.\n\
\n\
assertions\n\
+ Output the assertions after preprocessing and before clausification.\n\
  Can also specify \"assertions:pre-PASS\" or \"assertions:post-PASS\",\n\
  where PASS is one of the preprocessing passes: definition-expansion\n\
  boolean-terms constrain-subtypes substitution strings-pp skolem-quant\n\
  simplify static-learning ite-removal repeat-simplify\n\
  rewrite-apply-to-const theory-preprocessing.\n\
  PASS can also be the special value \"everything\", in which case the\n\
  assertions are printed before any preprocessing (with\n\
  \"assertions:pre-everything\") or after all preprocessing completes\n\
  (with \"assertions:post-everything\").\n\
\n\
clauses\n\
+ Do all the preprocessing outlined above, and dump the CNF-converted\n\
  output\n\
\n\
state\n\
+ Dump all contextual assertions (e.g., SAT decisions, propagations..).\n\
  Implied by all \"stateful\" modes below and conflicts with all\n\
  non-stateful modes below.\n\
\n\
t-conflicts [non-stateful]\n\
+ Output correctness queries for all theory conflicts\n\
\n\
missed-t-conflicts [stateful]\n\
+ Output completeness queries for theory conflicts\n\
\n\
t-propagations [stateful]\n\
+ Output correctness queries for all theory propagations\n\
\n\
missed-t-propagations [stateful]\n\
+ Output completeness queries for theory propagations (LARGE and EXPENSIVE)\n\
\n\
t-lemmas [non-stateful]\n\
+ Output correctness queries for all theory lemmas\n\
\n\
t-explanations [non-stateful]\n\
+ Output correctness queries for all theory explanations\n\
\n\
bv-rewrites [non-stateful]\n\
+ Output correctness queries for all bitvector rewrites\n\
\n\
bv-abstraction [non-stateful]\n\
+ Output correctness queries for all bv abstraction \n\
\n\
bv-algebraic [non-stateful]\n\
+ Output correctness queries for bv algebraic solver. \n\
\n\
theory::fullcheck [non-stateful]\n                                      \
+ Output completeness queries for all full-check effort-level theory checks\n\
\n\
Dump modes can be combined with multiple uses of --dump.  Generally you want\n\
one from the assertions category (either assertions or clauses), and\n\
perhaps one or more stateful or non-stateful modes for checking correctness\n\
and completeness of decision procedure implementations.  Stateful modes dump\n\
the contextual assertions made by the core solver (all decisions and\n\
propagations as assertions; that affects the validity of the resulting\n\
correctness and completeness queries, so of course stateful and non-stateful\n\
modes cannot be mixed in the same run.\n\
\n\
The --output-language option controls the language used for dumping, and\n\
this allows you to connect CVC4 to another solver implementation via a UNIX\n\
pipe to perform on-line checking.  The --dump-to option can be used to dump\n\
to a file.\n\
";

const std::string SmtOptionsHandler::s_simplificationHelp = "\
Simplification modes currently supported by the --simplification option:\n\
\n\
batch (default) \n\
+ save up all ASSERTions; run nonclausal simplification and clausal\n\
  (MiniSat) propagation for all of them only after reaching a querying command\n\
  (CHECKSAT or QUERY or predicate SUBTYPE declaration)\n\
\n\
none\n\
+ do not perform nonclausal simplification\n\
";

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

LogicInfo* SmtOptionsHandler::stringToLogicInfo(std::string option, std::string optarg) throw(OptionException) {
  try {
#warning "TODO: Fix the blatant memory leak here"
    LogicInfo* logic = new LogicInfo(optarg);
    if(d_smtEngine != NULL) {
      d_smtEngine->setLogic(*logic);
    }
    return logic;
  } catch(IllegalArgumentException& e) {
    throw OptionException(std::string("invalid logic specification for --force-logic: `") +
                          optarg + "':\n" + e.what());
  }
}

SimplificationMode SmtOptionsHandler::stringToSimplificationMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "batch") {
    return SIMPLIFICATION_MODE_BATCH;
  } else if(optarg == "none") {
    return SIMPLIFICATION_MODE_NONE;
  } else if(optarg == "help") {
    puts(s_simplificationHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --simplification: `") +
                          optarg + "'.  Try --simplification help.");
  }
}


void SmtOptionsHandler::beforeSearch(std::string option, bool value) throw(ModalException) {
  SmtEngine::beforeSearch(d_smtEngine, option);
}

void SmtOptionsHandler::setProduceAssertions(std::string option, bool value) throw() {
  options::produceAssertions.set(value);
  options::interactiveMode.set(value);
}


void SmtOptionsHandler::proofEnabledBuild(std::string option, bool value) throw(OptionException) {
#if !(IS_PROOFS_BUILD)
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a proofs-enabled build of CVC4; this binary was not built with proof support";
    throw OptionException(ss.str());
  }
#endif /* IS_PROOFS_BUILD */
}


// This macro is used for setting :regular-output-channel and :diagnostic-output-channel
// to redirect a stream.  It maintains all attributes set on the stream.
#define __CVC4__SMT__OUTPUTCHANNELS__SETSTREAM__(__channel_get, __channel_set) \
  { \
    int dagSetting = expr::ExprDag::getDag(__channel_get); \
    size_t exprDepthSetting = expr::ExprSetDepth::getDepth(__channel_get); \
    bool printtypesSetting = expr::ExprPrintTypes::getPrintTypes(__channel_get); \
    OutputLanguage languageSetting = expr::ExprSetLanguage::getLanguage(__channel_get); \
    __channel_set; \
    __channel_get << Expr::dag(dagSetting); \
    __channel_get << Expr::setdepth(exprDepthSetting); \
    __channel_get << Expr::printtypes(printtypesSetting); \
    __channel_get << Expr::setlanguage(languageSetting); \
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



std::string SmtOptionsHandler::checkReplayFilename(std::string option, std::string optarg) {
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --replay"));
  } else {
    return optarg;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

std::ostream* SmtOptionsHandler::checkReplayLogFilename(std::string option, std::string optarg) {
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --replay-log"));
  } else if(optarg == "-") {
    return &std::cout;
  } else if(!options::filesystemAccess()) {
    throw OptionException(std::string("Filesystem access not permitted"));
  } else {
    errno = 0;
    std::ostream* replayLog = new std::ofstream(optarg.c_str(), std::ofstream::out | std::ofstream::trunc);
    if(replayLog == NULL || !*replayLog) {
      std::stringstream ss;
      ss << "Cannot open replay-log file: `" << optarg << "': " << __cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
    return replayLog;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}

void SmtOptionsHandler::statsEnabledBuild(std::string option, bool value) throw(OptionException) {
#ifndef CVC4_STATISTICS_ON
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a statistics-enabled build of CVC4; this binary was not built with statistics support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_STATISTICS_ON */
}

unsigned long SmtOptionsHandler::tlimitHandler(std::string option, std::string optarg) throw(OptionException)  {
  unsigned long ms;
  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }

  // make sure the resource is set if the option is updated
  // if the smt engine is null the resource will be set in the
  if (d_smtEngine != NULL) {
    ResourceManager* rm = NodeManager::fromExprManager(d_smtEngine->getExprManager())->getResourceManager();
    rm->setTimeLimit(ms, true);
  }
  return ms;
}

unsigned long SmtOptionsHandler::tlimitPerHandler(std::string option, std::string optarg) throw(OptionException) {
  unsigned long ms;

  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }

  if (d_smtEngine != NULL) {
    ResourceManager* rm = NodeManager::fromExprManager(d_smtEngine->getExprManager())->getResourceManager();
    rm->setTimeLimit(ms, false);
  }
  return ms;
}

unsigned long SmtOptionsHandler::rlimitHandler(std::string option, std::string optarg) throw(OptionException) {
  unsigned long ms;

  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }

  if (d_smtEngine != NULL) {
    ResourceManager* rm = NodeManager::fromExprManager(d_smtEngine->getExprManager())->getResourceManager();
    rm->setResourceLimit(ms, true);
  }
  return ms;
}

unsigned long SmtOptionsHandler::rlimitPerHandler(std::string option, std::string optarg) throw(OptionException) {
  unsigned long ms;

  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }

  // TODO: Remove check?
  if (d_smtEngine != NULL) {
    ResourceManager* rm = NodeManager::fromExprManager(d_smtEngine->getExprManager())->getResourceManager();
    rm->setResourceLimit(ms, false);
  }
  return ms;
}



// expr/options_handlers.h
void SmtOptionsHandler::setDefaultExprDepth(std::string option, int depth) {
  if(depth < -1) {
    throw OptionException("--default-expr-depth requires a positive argument, or -1.");
  }

  Debug.getStream() << Expr::setdepth(depth);
  Trace.getStream() << Expr::setdepth(depth);
  Notice.getStream() << Expr::setdepth(depth);
  Chat.getStream() << Expr::setdepth(depth);
  Message.getStream() << Expr::setdepth(depth);
  Warning.getStream() << Expr::setdepth(depth);
  // intentionally exclude Dump stream from this list
}

void SmtOptionsHandler::setDefaultDagThresh(std::string option, int dag) {
  if(dag < 0) {
    throw OptionException("--default-dag-thresh requires a nonnegative argument.");
  }

  Debug.getStream() << Expr::dag(dag);
  Trace.getStream() << Expr::dag(dag);
  Notice.getStream() << Expr::dag(dag);
  Chat.getStream() << Expr::dag(dag);
  Message.getStream() << Expr::dag(dag);
  Warning.getStream() << Expr::dag(dag);
  Dump.getStream() << Expr::dag(dag);
}

void SmtOptionsHandler::setPrintExprTypes(std::string option) {
  Debug.getStream() << Expr::printtypes(true);
  Trace.getStream() << Expr::printtypes(true);
  Notice.getStream() << Expr::printtypes(true);
  Chat.getStream() << Expr::printtypes(true);
  Message.getStream() << Expr::printtypes(true);
  Warning.getStream() << Expr::printtypes(true);
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

std::string SmtOptionsHandler::__cvc4_errno_failreason() {
#if HAVE_STRERROR_R
#if STRERROR_R_CHAR_P
  if(errno != 0) {
    // GNU version of strerror_r: *might* use the given buffer,
    // or might not.  It returns a pointer to buf, or not.
    char buf[80];
    return std::string(strerror_r(errno, buf, sizeof buf));
  } else {
    return "unknown reason";
  }
#else /* STRERROR_R_CHAR_P */
  if(errno != 0) {
    // XSI version of strerror_r: always uses the given buffer.
    // Returns an error code.
    char buf[80];
    if(strerror_r(errno, buf, sizeof buf) == 0) {
      return std::string(buf);
    } else {
      // some error occurred while getting the error string
      return "unknown reason";
    }
  } else {
    return "unknown reason";
  }
#endif /* STRERROR_R_CHAR_P */
#else /* HAVE_STRERROR_R */
  return "unknown reason";
#endif /* HAVE_STRERROR_R */
}

}/* CVC4::smt namespace */
}/* CVC4 namespace */
