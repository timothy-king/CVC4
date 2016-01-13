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

#include "options/options_handler_interface.h"

#include <ostream>
#include <string>
#include <cerrno>

#include "cvc4autoconfig.h"

#include "base/configuration.h"
#include "base/cvc4_assert.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
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
#include "options/didyoumean.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/printer_modes.h"
#include "options/quantifiers_modes.h"
#include "options/simplification_mode.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "options/theoryof_mode.h"
#include "options/ufss_mode.h"

namespace CVC4 {
namespace options {

// theory/arith/options_handlers.h
const std::string OptionsHandler::s_arithUnateLemmasHelp = "\
Unate lemmas are generated before SAT search begins using the relationship\n\
of constant terms and polynomials.\n\
Modes currently supported by the --unate-lemmas option:\n\
+ none \n\
+ ineqs \n\
  Outputs lemmas of the general form (<= p c) implies (<= p d) for c < d.\n\
+ eqs \n\
  Outputs lemmas of the general forms\n\
  (= p c) implies (<= p d) for c < d, or\n\
  (= p c) implies (not (= p d)) for c != d.\n\
+ all \n\
  A combination of inequalities and equalities.\n\
";

const std::string OptionsHandler::s_arithPropagationModeHelp = "\
This decides on kind of propagation arithmetic attempts to do during the search.\n\
+ none\n\
+ unate\n\
 use constraints to do unate propagation\n\
+ bi (Bounds Inference)\n\
  infers bounds on basic variables using the upper and lower bounds of the\n\
  non-basic variables in the tableau.\n\
+both\n\
";

const std::string OptionsHandler::s_errorSelectionRulesHelp = "\
This decides on the rule used by simplex during heuristic rounds\n\
for deciding the next basic variable to select.\n\
Heuristic pivot rules available:\n\
+min\n\
  The minimum abs() value of the variable's violation of its bound. (default)\n\
+max\n\
  The maximum violation the bound\n\
+varord\n\
  The variable order\n\
";

ArithUnateLemmaMode OptionsHandler::stringToArithUnateLemmaMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "all") {
    return ALL_PRESOLVE_LEMMAS;
  } else if(optarg == "none") {
    return NO_PRESOLVE_LEMMAS;
  } else if(optarg == "ineqs") {
    return INEQUALITY_PRESOLVE_LEMMAS;
  } else if(optarg == "eqs") {
    return EQUALITY_PRESOLVE_LEMMAS;
  } else if(optarg == "help") {
    puts(s_arithUnateLemmasHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --unate-lemmas: `") +
                          optarg + "'.  Try --unate-lemmas help.");
  }
}

ArithPropagationMode OptionsHandler::stringToArithPropagationMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "none") {
    return NO_PROP;
  } else if(optarg == "unate") {
    return UNATE_PROP;
  } else if(optarg == "bi") {
    return BOUND_INFERENCE_PROP;
  } else if(optarg == "both") {
    return BOTH_PROP;
  } else if(optarg == "help") {
    puts(s_arithPropagationModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --arith-prop: `") +
                          optarg + "'.  Try --arith-prop help.");
  }
}

ErrorSelectionRule OptionsHandler::stringToErrorSelectionRule(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "min") {
    return MINIMUM_AMOUNT;
  } else if(optarg == "varord") {
    return VAR_ORDER;
  } else if(optarg == "max") {
    return MAXIMUM_AMOUNT;
  } else if(optarg == "help") {
    puts(s_errorSelectionRulesHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --heuristic-pivot-rule: `") +
                          optarg + "'.  Try --heuristic-pivot-rule help.");
  }
}
// theory/quantifiers/options_handlers.h

const std::string OptionsHandler::s_instWhenHelp = "\
Modes currently supported by the --inst-when option:\n\
\n\
full-last-call (default)\n\
+ Alternate running instantiation rounds at full effort and last\n\
  call.  In other words, interleave instantiation and theory combination.\n\
\n\
full\n\
+ Run instantiation round at full effort, before theory combination.\n\
\n\
full-delay \n\
+ Run instantiation round at full effort, before theory combination, after\n\
  all other theories have finished.\n\
\n\
full-delay-last-call \n\
+ Alternate running instantiation rounds at full effort after all other\n\
  theories have finished, and last call.  \n\
\n\
last-call\n\
+ Run instantiation at last call effort, after theory combination and\n\
  and theories report sat.\n\
\n\
";

const std::string OptionsHandler::s_literalMatchHelp = "\
Literal match modes currently supported by the --literal-match option:\n\
\n\
none (default)\n\
+ Do not use literal matching.\n\
\n\
predicate\n\
+ Consider the phase requirements of predicate literals when applying heuristic\n\
  quantifier instantiation.  For example, the trigger P( x ) in the quantified \n\
  formula forall( x ). ( P( x ) V ~Q( x ) ) will only be matched with ground\n\
  terms P( t ) where P( t ) is in the equivalence class of false, and likewise\n\
  Q( x ) with Q( s ) where Q( s ) is in the equivalence class of true.\n\
\n\
";

const std::string OptionsHandler::s_mbqiModeHelp = "\
Model-based quantifier instantiation modes currently supported by the --mbqi option:\n\
\n\
default \n\
+ Use algorithm from Section 5.4.2 of thesis Finite Model Finding in Satisfiability \n\
  Modulo Theories.\n\
\n\
none \n\
+ Disable model-based quantifier instantiation.\n\
\n\
gen-ev \n\
+ Use model-based quantifier instantiation algorithm from CADE 24 finite\n\
  model finding paper based on generalizing evaluations.\n\
\n\
fmc-interval \n\
+ Same as default, but with intervals for models of integer functions.\n\
\n\
abs \n\
+ Use abstract MBQI algorithm (uses disjoint sets). \n\
\n\
";

const std::string OptionsHandler::s_qcfWhenModeHelp = "\
Quantifier conflict find modes currently supported by the --quant-cf-when option:\n\
\n\
default \n\
+ Default, apply conflict finding at full effort.\n\
\n\
last-call \n\
+ Apply conflict finding at last call, after theory combination and \n\
  and all theories report sat. \n\
\n\
std \n\
+ Apply conflict finding at standard effort.\n\
\n\
std-h \n\
+ Apply conflict finding at standard effort when heuristic says to. \n\
\n\
";

const std::string OptionsHandler::s_qcfModeHelp = "\
Quantifier conflict find modes currently supported by the --quant-cf option:\n\
\n\
prop-eq \n\
+ Default, apply QCF algorithm to propagate equalities as well as conflicts. \n\
\n\
conflict \n\
+ Apply QCF algorithm to find conflicts only.\n\
\n\
partial \n\
+ Apply QCF algorithm to instantiate heuristically as well. \n\
\n\
mc \n\
+ Apply QCF algorithm in a complete way, so that a model is ensured when it fails. \n\
\n\
";

const std::string OptionsHandler::s_userPatModeHelp = "\
User pattern modes currently supported by the --user-pat option:\n\
\n\
trust \n\
+ When provided, use only user-provided patterns for a quantified formula.\n\
\n\
use \n\
+ Use both user-provided and auto-generated patterns when patterns\n\
  are provided for a quantified formula.\n\
\n\
resort \n\
+ Use user-provided patterns only after auto-generated patterns saturate.\n\
\n\
ignore \n\
+ Ignore user-provided patterns. \n\
\n\
interleave \n\
+ Alternate between use/resort. \n\
\n\
";

const std::string OptionsHandler::s_triggerSelModeHelp = "\
Trigger selection modes currently supported by the --trigger-sel option:\n\
\n\
default \n\
+ Default, consider all subterms of quantified formulas for trigger selection.\n\
\n\
min \n\
+ Consider only minimal subterms that meet criteria for triggers.\n\
\n\
max \n\
+ Consider only maximal subterms that meet criteria for triggers. \n\
\n\
";
const std::string OptionsHandler::s_prenexQuantModeHelp = "\
Prenex quantifiers modes currently supported by the --prenex-quant option:\n\
\n\
default \n\
+ Default, prenex all nested quantifiers except those with user patterns.\n\
\n\
all \n\
+ Prenex all nested quantifiers.\n\
\n\
none \n\
+ Do no prenex nested quantifiers. \n\
\n\
";

const std::string OptionsHandler::s_cegqiFairModeHelp = "\
Modes for enforcing fairness for counterexample guided quantifier instantion, supported by --cegqi-fair:\n\
\n\
uf-dt-size \n\
+ Enforce fairness using an uninterpreted function for datatypes size.\n\
\n\
default | dt-size \n\
+ Default, enforce fairness using size theory operator.\n\
\n\
dt-height-bound \n\
+ Enforce fairness by height bound predicate.\n\
\n\
none \n\
+ Do not enforce fairness. \n\
\n\
";

const std::string OptionsHandler::s_termDbModeHelp = "\
Modes for term database, supported by --term-db-mode:\n\
\n\
all  \n\
+ Quantifiers module considers all ground terms.\n\
\n\
relevant \n\
+ Quantifiers module considers only ground terms connected to current assertions. \n\
\n\
";

const std::string OptionsHandler::s_iteLiftQuantHelp = "\
Modes for term database, supported by --ite-lift-quant:\n\
\n\
none  \n\
+ Do not lift if-then-else in quantified formulas.\n\
\n\
simple  \n\
+ Lift if-then-else in quantified formulas if results in smaller term size.\n\
\n\
all \n\
+ Lift if-then-else in quantified formulas. \n\
\n\
";

const std::string OptionsHandler::s_sygusInvTemplHelp = "\
Template modes for sygus invariant synthesis, supported by --sygus-inv-templ:\n\
\n\
none  \n\
+ Synthesize invariant directly.\n\
\n\
pre  \n\
+ Synthesize invariant based on weakening of precondition .\n\
\n\
post \n\
+ Synthesize invariant based on strengthening of postcondition. \n\
\n\
";

const std::string OptionsHandler::s_macrosQuantHelp = "\
Template modes for quantifiers macro expansion, supported by --macros-quant-mode:\n\
\n\
all \n\
+ Infer definitions for functions, including those containing quantified formulas.\n\
\n\
ground (default) \n\
+ Only infer ground definitions for functions.\n\
\n\
ground-uf \n\
+ Only infer ground definitions for functions that result in triggers for all free variables.\n\
\n\
";

theory::quantifiers::InstWhenMode OptionsHandler::stringToInstWhenMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "pre-full") {
    return theory::quantifiers::INST_WHEN_PRE_FULL;
  } else if(optarg == "full") {
    return theory::quantifiers::INST_WHEN_FULL;
  } else if(optarg == "full-delay") {
    return theory::quantifiers::INST_WHEN_FULL_DELAY;
  } else if(optarg == "full-last-call") {
    return theory::quantifiers::INST_WHEN_FULL_LAST_CALL;
  } else if(optarg == "full-delay-last-call") {
    return theory::quantifiers::INST_WHEN_FULL_DELAY_LAST_CALL;
  } else if(optarg == "last-call") {
    return theory::quantifiers::INST_WHEN_LAST_CALL;
  } else if(optarg == "help") {
    puts(s_instWhenHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --inst-when: `") +
                          optarg + "'.  Try --inst-when help.");
  }
}

void OptionsHandler::checkInstWhenMode(std::string option, theory::quantifiers::InstWhenMode mode) throw(OptionException)  {
  if(mode == theory::quantifiers::INST_WHEN_PRE_FULL) {
    throw OptionException(std::string("Mode pre-full for ") + option + " is not supported in this release.");
  }
}

theory::quantifiers::LiteralMatchMode OptionsHandler::stringToLiteralMatchMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg ==  "none") {
    return theory::quantifiers::LITERAL_MATCH_NONE;
  } else if(optarg ==  "predicate") {
    return theory::quantifiers::LITERAL_MATCH_PREDICATE;
  } else if(optarg ==  "equality") {
    return theory::quantifiers::LITERAL_MATCH_EQUALITY;
  } else if(optarg ==  "help") {
    puts(s_literalMatchHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --literal-matching: `") +
                          optarg + "'.  Try --literal-matching help.");
  }
}

void OptionsHandler::checkLiteralMatchMode(std::string option, theory::quantifiers::LiteralMatchMode mode) throw(OptionException) {
  if(mode == theory::quantifiers::LITERAL_MATCH_EQUALITY) {
    throw OptionException(std::string("Mode equality for ") + option + " is not supported in this release.");
  }
}

theory::quantifiers::MbqiMode OptionsHandler::stringToMbqiMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "gen-ev") {
    return theory::quantifiers::MBQI_GEN_EVAL;
  } else if(optarg == "none") {
    return theory::quantifiers::MBQI_NONE;
  } else if(optarg == "default" || optarg ==  "fmc") {
    return theory::quantifiers::MBQI_FMC;
  } else if(optarg == "fmc-interval") {
    return theory::quantifiers::MBQI_FMC_INTERVAL;
  } else if(optarg == "abs") {
    return theory::quantifiers::MBQI_ABS;
  } else if(optarg == "trust") {
    return theory::quantifiers::MBQI_TRUST;
  } else if(optarg == "help") {
    puts(s_mbqiModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --mbqi: `") +
                          optarg + "'.  Try --mbqi help.");
  }
}


void OptionsHandler::checkMbqiMode(std::string option, theory::quantifiers::MbqiMode mode) throw(OptionException) {}


theory::quantifiers::QcfWhenMode OptionsHandler::stringToQcfWhenMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg ==  "default") {
    return theory::quantifiers::QCF_WHEN_MODE_DEFAULT;
  } else if(optarg ==  "last-call") {
    return theory::quantifiers::QCF_WHEN_MODE_LAST_CALL;
  } else if(optarg ==  "std") {
    return theory::quantifiers::QCF_WHEN_MODE_STD;
  } else if(optarg ==  "std-h") {
    return theory::quantifiers::QCF_WHEN_MODE_STD_H;
  } else if(optarg ==  "help") {
    puts(s_qcfWhenModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --quant-cf-when: `") +
                          optarg + "'.  Try --quant-cf-when help.");
  }
}

theory::quantifiers::QcfMode OptionsHandler::stringToQcfMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg ==  "conflict") {
    return theory::quantifiers::QCF_CONFLICT_ONLY;
  } else if(optarg ==  "default" || optarg == "prop-eq") {
    return theory::quantifiers::QCF_PROP_EQ;
  } else if(optarg == "partial") {
    return theory::quantifiers::QCF_PARTIAL;
  } else if(optarg == "mc" ) {
    return theory::quantifiers::QCF_MC;
  } else if(optarg ==  "help") {
    puts(s_qcfModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --quant-cf-mode: `") +
                          optarg + "'.  Try --quant-cf-mode help.");
  }
}

theory::quantifiers::UserPatMode OptionsHandler::stringToUserPatMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "use") {
    return theory::quantifiers::USER_PAT_MODE_USE;
  } else if(optarg ==  "default" || optarg == "trust") {
    return theory::quantifiers::USER_PAT_MODE_TRUST;
  } else if(optarg == "resort") {
    return theory::quantifiers::USER_PAT_MODE_RESORT;
  } else if(optarg == "ignore") {
    return theory::quantifiers::USER_PAT_MODE_IGNORE;
  } else if(optarg == "interleave") {
    return theory::quantifiers::USER_PAT_MODE_INTERLEAVE;
  } else if(optarg ==  "help") {
    puts(s_userPatModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --user-pat: `") +
                          optarg + "'.  Try --user-pat help.");
  }
}

theory::quantifiers::TriggerSelMode OptionsHandler::stringToTriggerSelMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg ==  "default" || optarg == "all" ) {
    return theory::quantifiers::TRIGGER_SEL_DEFAULT;
  } else if(optarg == "min") {
    return theory::quantifiers::TRIGGER_SEL_MIN;
  } else if(optarg == "max") {
    return theory::quantifiers::TRIGGER_SEL_MAX;
  } else if(optarg ==  "help") {
    puts(s_triggerSelModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --trigger-sel: `") +
                          optarg + "'.  Try --trigger-sel help.");
  }
}


theory::quantifiers::PrenexQuantMode OptionsHandler::stringToPrenexQuantMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg ==  "default" ) {
    return theory::quantifiers::PRENEX_NO_USER_PAT;
  } else if(optarg == "all") {
    return theory::quantifiers::PRENEX_ALL;
  } else if(optarg == "none") {
    return theory::quantifiers::PRENEX_NONE;
  } else if(optarg ==  "help") {
    puts(s_prenexQuantModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --prenex-quant: `") +
                          optarg + "'.  Try --prenex-quant help.");
  }
}

theory::quantifiers::CegqiFairMode OptionsHandler::stringToCegqiFairMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "uf-dt-size" ) {
    return theory::quantifiers::CEGQI_FAIR_UF_DT_SIZE;
  } else if(optarg == "default" || optarg == "dt-size") {
    return theory::quantifiers::CEGQI_FAIR_DT_SIZE;
  } else if(optarg == "dt-height-bound" ){
    return theory::quantifiers::CEGQI_FAIR_DT_HEIGHT_PRED;
  } else if(optarg == "none") {
    return theory::quantifiers::CEGQI_FAIR_NONE;
  } else if(optarg ==  "help") {
    puts(s_cegqiFairModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --cegqi-fair: `") +
                          optarg + "'.  Try --cegqi-fair help.");
  }
}

theory::quantifiers::TermDbMode OptionsHandler::stringToTermDbMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "all" ) {
    return theory::quantifiers::TERM_DB_ALL;
  } else if(optarg == "relevant") {
    return theory::quantifiers::TERM_DB_RELEVANT;
  } else if(optarg ==  "help") {
    puts(s_termDbModeHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --term-db-mode: `") +
                          optarg + "'.  Try --term-db-mode help.");
  }
}

theory::quantifiers::IteLiftQuantMode OptionsHandler::stringToIteLiftQuantMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "all" ) {
    return theory::quantifiers::ITE_LIFT_QUANT_MODE_ALL;
  } else if(optarg == "simple") {
    return theory::quantifiers::ITE_LIFT_QUANT_MODE_SIMPLE;
  } else if(optarg == "none") {
    return theory::quantifiers::ITE_LIFT_QUANT_MODE_NONE;
  } else if(optarg ==  "help") {
    puts(s_iteLiftQuantHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --ite-lift-quant: `") +
                          optarg + "'.  Try --ite-lift-quant help.");
  }
}

theory::quantifiers::SygusInvTemplMode OptionsHandler::stringToSygusInvTemplMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "none" ) {
    return theory::quantifiers::SYGUS_INV_TEMPL_MODE_NONE;
  } else if(optarg == "pre") {
    return theory::quantifiers::SYGUS_INV_TEMPL_MODE_PRE;
  } else if(optarg == "post") {
    return theory::quantifiers::SYGUS_INV_TEMPL_MODE_POST;
  } else if(optarg ==  "help") {
    puts(s_sygusInvTemplHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --sygus-inv-templ: `") +
                          optarg + "'.  Try --sygus-inv-templ help.");
  }
}

theory::quantifiers::MacrosQuantMode OptionsHandler::stringToMacrosQuantMode(std::string option, std::string optarg) throw(OptionException) {
  if(optarg == "all" ) {
    return theory::quantifiers::MACROS_QUANT_MODE_ALL;
  } else if(optarg == "ground") {
    return theory::quantifiers::MACROS_QUANT_MODE_GROUND;
  } else if(optarg == "ground-uf") {
    return theory::quantifiers::MACROS_QUANT_MODE_GROUND_UF;
  } else if(optarg ==  "help") {
    puts(s_macrosQuantHelp.c_str());
    exit(1);
  } else {
    throw OptionException(std::string("unknown option for --macros-quant-mode: `") +
                          optarg + "'.  Try --macros-quant-mode help.");
  }
}


// theory/bv/options_handlers.h
void OptionsHandler::abcEnabledBuild(std::string option, bool value) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

void OptionsHandler::abcEnabledBuild(std::string option, std::string value) throw(OptionException) {
#ifndef CVC4_USE_ABC
  if(!value.empty()) {
    std::stringstream ss;
    ss << "option `" << option << "' requires an abc-enabled build of CVC4; this binary was not built with abc support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_USE_ABC */
}

const std::string OptionsHandler::s_bitblastingModeHelp = "\
Bit-blasting modes currently supported by the --bitblast option:\n\
\n\
lazy (default)\n\
+ Separate boolean structure and term reasoning betwen the core\n\
  SAT solver and the bv SAT solver\n\
\n\
eager\n\
+ Bitblast eagerly to bv SAT solver\n\
";

theory::bv::BitblastMode OptionsHandler::stringToBitblastMode(std::string option, std::string optarg) throw(OptionException) {
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

const std::string OptionsHandler::s_bvSlicerModeHelp = "\
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

theory::bv::BvSlicerMode OptionsHandler::stringToBvSlicerMode(std::string option, std::string optarg) throw(OptionException) {
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

void OptionsHandler::setBitblastAig(std::string option, bool arg) throw(OptionException) {
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
const std::string OptionsHandler::s_booleanTermConversionModeHelp = "\
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

theory::booleans::BooleanTermConversionMode OptionsHandler::stringToBooleanTermConversionMode(std::string option, std::string optarg) throw(OptionException){
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
const std::string OptionsHandler::s_ufssModeHelp = "\
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

theory::uf::UfssMode OptionsHandler::stringToUfssMode(std::string option, std::string optarg) throw(OptionException) {
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
const std::string OptionsHandler::s_theoryOfModeHelp = "\
TheoryOf modes currently supported by the --theoryof-mode option:\n\
\n\
type (default) \n\
+ type variables, constants and equalities by type\n\
\n\
term \n\
+ type variables as uninterpreted, equalities by the parametric theory\n\
";

theory::TheoryOfMode OptionsHandler::stringToTheoryOfMode(std::string option, std::string optarg) {
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

// theory/options_handlers.h
std::string OptionsHandler::handleUseTheoryList(std::string option, std::string optarg) {
  std::string currentList = options::useTheoryList();
  if(currentList.empty()){
    return optarg;
  } else {
    return currentList +','+ optarg;
  }
}

void OptionsHandler::notifyUseTheoryList(std::string option) {
  d_options->d_useTheoryListListeners.notify();
}



// printer/options_handlers.h
const std::string OptionsHandler::s_modelFormatHelp = "\
Model format modes currently supported by the --model-format option:\n\
\n\
default \n\
+ Print model as expressions in the output language format.\n\
\n\
table\n\
+ Print functional expressions over finite domains in a table format.\n\
";

const std::string OptionsHandler::s_instFormatHelp = "\
Inst format modes currently supported by the --model-format option:\n\
\n\
default \n\
+ Print instantiations as a list in the output language format.\n\
\n\
szs\n\
+ Print instantiations as SZS compliant proof.\n\
";

ModelFormatMode OptionsHandler::stringToModelFormatMode(std::string option, std::string optarg) throw(OptionException) {
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

InstFormatMode OptionsHandler::stringToInstFormatMode(std::string option, std::string optarg) throw(OptionException) {
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
const std::string OptionsHandler::s_decisionModeHelp = "\
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

decision::DecisionMode OptionsHandler::stringToDecisionMode(std::string option, std::string optarg) throw(OptionException) {
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

decision::DecisionWeightInternal OptionsHandler::stringToDecisionWeightInternal(std::string option, std::string optarg) throw(OptionException) {
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
const std::string OptionsHandler::s_dumpHelp = "\
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

const std::string OptionsHandler::s_simplificationHelp = "\
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



SimplificationMode OptionsHandler::stringToSimplificationMode(std::string option, std::string optarg) throw(OptionException) {
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


void OptionsHandler::setProduceAssertions(std::string option, bool value) throw() {
  options::produceAssertions.set(value);
  options::interactiveMode.set(value);
}


void OptionsHandler::proofEnabledBuild(std::string option, bool value) throw(OptionException) {
#ifndef CVC4_PROOF
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a proofs-enabled build of CVC4; this binary was not built with proof support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_PROOF */
}



std::string OptionsHandler::checkReplayFilename(std::string option, std::string optarg) {
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException (std::string("Bad file name for --replay"));
  } else {
    return optarg;
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}


void OptionsHandler::statsEnabledBuild(std::string option, bool value) throw(OptionException) {
#ifndef CVC4_STATISTICS_ON
  if(value) {
    std::stringstream ss;
    ss << "option `" << option << "' requires a statistics-enabled build of CVC4; this binary was not built with statistics support";
    throw OptionException(ss.str());
  }
#endif /* CVC4_STATISTICS_ON */
}

void OptionsHandler::threadN(std::string option) {
  throw OptionException(option + " is not a real option by itself.  Use e.g. --thread0=\"--random-seed=10 --random-freq=0.02\" --thread1=\"--random-seed=20 --random-freq=0.05\"");
}

// main/options_handlers.h
void OptionsHandler::showConfiguration(std::string option) {
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

void OptionsHandler::showDebugTags(std::string option) {
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

void OptionsHandler::showTraceTags(std::string option) {
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


OutputLanguage OptionsHandler::stringToOutputLanguage(std::string option, std::string optarg) throw(OptionException) {
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

InputLanguage OptionsHandler::stringToInputLanguage(std::string option, std::string optarg) throw(OptionException) {
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

/* options/base_options_handlers.h */
void OptionsHandler::setVerbosity(std::string option, int value) throw(OptionException) {
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

void OptionsHandler::increaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() + 1);
  setVerbosity(option, options::verbosity());
}

void OptionsHandler::decreaseVerbosity(std::string option) {
  options::verbosity.set(options::verbosity() - 1);
  setVerbosity(option, options::verbosity());
}


void OptionsHandler::addTraceTag(std::string option, std::string optarg) {
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

void OptionsHandler::addDebugTag(std::string option, std::string optarg) {
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




std::string OptionsHandler::suggestTags(char const* const* validTags, std::string inputTag,
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


std::string OptionsHandler::__cvc4_errno_failreason() {
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

// theory/arith/options_handlers.h
ArithUnateLemmaMode stringToArithUnateLemmaMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToArithUnateLemmaMode(option, optarg);
}
ArithPropagationMode stringToArithPropagationMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToArithPropagationMode(option, optarg);
}
ErrorSelectionRule stringToErrorSelectionRule(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToErrorSelectionRule(option, optarg);
}

// theory/quantifiers/options_handlers.h
theory::quantifiers::InstWhenMode stringToInstWhenMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToInstWhenMode(option, optarg);
}
void checkInstWhenMode(std::string option, theory::quantifiers::InstWhenMode mode,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->checkInstWhenMode(option, mode);
}
theory::quantifiers::LiteralMatchMode stringToLiteralMatchMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToLiteralMatchMode(option, optarg);
}
void checkLiteralMatchMode(std::string option, theory::quantifiers::LiteralMatchMode mode,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->checkLiteralMatchMode(option, mode);
}
theory::quantifiers::MbqiMode stringToMbqiMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToMbqiMode(option, optarg);
}
void checkMbqiMode(std::string option, theory::quantifiers::MbqiMode mode,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->checkMbqiMode(option, mode);
}
theory::quantifiers::QcfWhenMode stringToQcfWhenMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToQcfWhenMode(option, optarg);
}
theory::quantifiers::QcfMode stringToQcfMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToQcfMode(option, optarg);
}
theory::quantifiers::UserPatMode stringToUserPatMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToUserPatMode(option, optarg);
}
theory::quantifiers::TriggerSelMode stringToTriggerSelMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToTriggerSelMode(option, optarg);
}
theory::quantifiers::PrenexQuantMode stringToPrenexQuantMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToPrenexQuantMode(option, optarg);
}
theory::quantifiers::CegqiFairMode stringToCegqiFairMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToCegqiFairMode(option, optarg);
}
theory::quantifiers::TermDbMode stringToTermDbMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler-> stringToTermDbMode(option, optarg);
}
theory::quantifiers::IteLiftQuantMode stringToIteLiftQuantMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToIteLiftQuantMode(option, optarg);
}
theory::quantifiers::SygusInvTemplMode stringToSygusInvTemplMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToSygusInvTemplMode(option, optarg);
}
theory::quantifiers::MacrosQuantMode stringToMacrosQuantMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToMacrosQuantMode(option, optarg);
}


// theory/bv/options_handlers.h
void abcEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->abcEnabledBuild(option, value);
}
void abcEnabledBuild(std::string option, std::string value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->abcEnabledBuild(option, value);
}
theory::bv::BitblastMode stringToBitblastMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToBitblastMode(option, optarg);
}
theory::bv::BvSlicerMode stringToBvSlicerMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToBvSlicerMode(option, optarg);
}
void setBitblastAig(std::string option, bool arg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->setBitblastAig(option, arg);
}


// theory/booleans/options_handlers.h
theory::booleans::BooleanTermConversionMode stringToBooleanTermConversionMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToBooleanTermConversionMode( option, optarg);
}

// theory/uf/options_handlers.h
theory::uf::UfssMode stringToUfssMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToUfssMode(option, optarg);
}

// theory/options_handlers.h
theory::TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToTheoryOfMode(option, optarg);
}

std::string handleUseTheoryList(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->handleUseTheoryList(option, optarg);
}

void notifyUseTheoryList(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->notifyUseTheoryList(option);
}

// printer/options_handlers.h
ModelFormatMode stringToModelFormatMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToModelFormatMode(option, optarg);
}

InstFormatMode stringToInstFormatMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToInstFormatMode(option, optarg);
}


// decision/options_handlers.h
decision::DecisionMode stringToDecisionMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToDecisionMode(option, optarg);
}

decision::DecisionWeightInternal stringToDecisionWeightInternal(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToDecisionWeightInternal(option, optarg);
}


/* options/base_options_handlers.h */
void setVerbosity(std::string option, int value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->setVerbosity(option, value);
}
void increaseVerbosity(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->increaseVerbosity(option);
}
void decreaseVerbosity(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->decreaseVerbosity(option);
}

OutputLanguage stringToOutputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToOutputLanguage(option, optarg);
}

InputLanguage stringToInputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToInputLanguage(option, optarg);
}

void addTraceTag(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->addTraceTag(option, optarg);
}

void addDebugTag(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->addDebugTag(option, optarg);
}

void setPrintSuccess(std::string option, bool value, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->setPrintSuccess(option, value);
}


/* main/options_handlers.h */
void showConfiguration(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->showConfiguration(option);
}

void showDebugTags(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->showDebugTags(option);
}

void showTraceTags(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->showTraceTags(option);
}

void threadN(std::string option, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->threadN(option);
}

/* expr/options_handlers.h */
void setDefaultExprDepth(std::string option, int depth, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->setDefaultExprDepth(option, depth);
}

void setDefaultDagThresh(std::string option, int dag, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->setDefaultDagThresh(option, dag);
}

void setPrintExprTypes(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->setPrintExprTypes(option);
}


/* smt/options_handlers.h */
void dumpMode(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->dumpMode(option, optarg);
}

SimplificationMode stringToSimplificationMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException){
  PrettyCheckArgument(handler != NULL, handler);
  return handler->stringToSimplificationMode(option, optarg);
}

void notifyForceLogic(const std::string& option, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->notifyForceLogic(option);
}

// ensure we haven't started search yet
void notifyBeforeSearch(const std::string& option, OptionsHandler* handler)
    throw(ModalException)
{
  PrettyCheckArgument(handler != NULL, handler);
  handler->notifyBeforeSearch(option);
}

void setProduceAssertions(std::string option, bool value, OptionsHandler* handler) throw() {
  PrettyCheckArgument(handler != NULL, handler);
  handler->setProduceAssertions(option, value);
}

// ensure we are a proof-enabled build of CVC4
void proofEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->proofEnabledBuild(option, value);
}

void dumpToFile(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->dumpToFile(option, optarg);
}

void setRegularOutputChannel(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->setRegularOutputChannel(option, optarg);
}

void setDiagnosticOutputChannel(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  handler->setDiagnosticOutputChannel(option, optarg);
}

std::string checkReplayFilename(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->checkReplayFilename(option, optarg);
}


// ensure we are a stats-enabled build of CVC4
void statsEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->statsEnabledBuild(option, value);
}

unsigned long tlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->tlimitHandler(option, optarg);
}

unsigned long tlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler-> tlimitPerHandler(option, optarg);
}

unsigned long rlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->rlimitHandler(option, optarg);
}

unsigned long rlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler);
  return handler->rlimitPerHandler(option, optarg);
}


void notifyTlimit(const std::string& option, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->notifyTlimit(option);
}

void notifyTlimitPer(const std::string& option, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->notifyTlimitPer(option);
}

void notifyRlimit(const std::string& option, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->notifyRlimit(option);
}

void notifyRlimitPer(const std::string& option, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler);
  handler->notifyRlimitPer(option);
}



OptionsHandler::OptionsHandler(Options* options) : d_options(options) { }

void OptionsHandler::notifyForceLogic(const std::string& option){
  d_options->d_forceLogicListeners.notify();
}

void OptionsHandler::notifyBeforeSearch(const std::string& option)
    throw(ModalException)
{
  try{
    d_options->d_beforeSearchListeners.notify();
  } catch (ModalException&){
    std::stringstream ss;
    ss << "cannot change option `" << option
       << "' after final initialization (i.e., after logic has been set)";
    throw ModalException(ss.str());
  }
}


void OptionsHandler::notifyTlimit(const std::string& option) {
  d_options->d_tlimitListeners.notify();
}

void OptionsHandler::notifyTlimitPer(const std::string& option) {
  d_options->d_tlimitPerListeners.notify();
}

void OptionsHandler::notifyRlimit(const std::string& option) {
  d_options->d_rlimitListeners.notify();
}

void OptionsHandler::notifyRlimitPer(const std::string& option) {
  d_options->d_rlimitPerListeners.notify();
}


unsigned long OptionsHandler::tlimitHandler(std::string option, std::string optarg) throw(OptionException)  {
  unsigned long ms;
  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }
  return ms;
}

unsigned long OptionsHandler::tlimitPerHandler(std::string option, std::string optarg) throw(OptionException) {
  unsigned long ms;

  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }
  return ms;
}

unsigned long OptionsHandler::rlimitHandler(std::string option, std::string optarg) throw(OptionException) {
  unsigned long ms;

  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }
  return ms;
}


unsigned long OptionsHandler::rlimitPerHandler(std::string option, std::string optarg) throw(OptionException) {
  unsigned long ms;

  std::istringstream convert(optarg);
  if (!(convert >> ms)) {
    throw OptionException("option `"+option+"` requires a number as an argument");
  }

  return ms;
}


}/* CVC4::options namespace */
}/* CVC4 namespace */
