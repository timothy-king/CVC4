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
#include "theory/logic_info.h"

namespace CVC4 {
namespace smt {

class SmtOptionsHandler : public options::OptionsHandler {
public:
  SmtOptionsHandler(SmtEngine* smt);
  ~SmtOptionsHandler();

  // DONE
  // theory/bv/options_handlers.h
  // theory/booleans/options_handlers.h
  // theory/uf/options_handlers.h
  // theory/options_handlers.h
  // printer/options_handlers.h
  // decision/options_handlers.h
  // smt/options_handlers.h
  // expr/options_handlers.h
  // main/options_handlers.h
  // options/base_options_handlers.h

  // WORKING ON
  // theory/quantifiers/options_handlers.h

  // TODO
  // theory/arith/options_handlers.h


  // theory/arith/options_handlers.h
  virtual ArithUnateLemmaMode stringToArithUnateLemmaMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual ArithPropagationMode stringToArithPropagationMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual ErrorSelectionRule stringToErrorSelectionRule(std::string option, std::string optarg) throw(OptionException) = 0;

  // theory/quantifiers/options_handlers.h
  virtual theory::quantifiers::InstWhenMode stringToInstWhenMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual void checkInstWhenMode(std::string option, theory::quantifiers::InstWhenMode mode) throw(OptionException) = 0;
  virtual theory::quantifiers::LiteralMatchMode stringToLiteralMatchMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual void checkLiteralMatchMode(std::string option, theory::quantifiers::LiteralMatchMode mode) throw(OptionException) = 0;
  virtual theory::quantifiers::MbqiMode stringToMbqiMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual void checkMbqiMode(std::string option, theory::quantifiers::MbqiMode mode) throw(OptionException) = 0;
  virtual theory::quantifiers::QcfWhenMode stringToQcfWhenMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::QcfMode stringToQcfMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::UserPatMode stringToUserPatMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::TriggerSelMode stringToTriggerSelMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::PrenexQuantMode stringToPrenexQuantMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::CegqiFairMode stringToCegqiFairMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::TermDbMode stringToTermDbMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::IteLiftQuantMode stringToIteLiftQuantMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::SygusInvTemplMode stringToSygusInvTemplMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual theory::quantifiers::MacrosQuantMode stringToMacrosQuantMode(std::string option, std::string optarg) throw(OptionException) = 0;

  // theory/bv/options_handlers.h
  virtual void abcEnabledBuild(std::string option, bool value) throw(OptionException);
  virtual void abcEnabledBuild(std::string option, std::string value) throw(OptionException);
  virtual theory::bv::BitblastMode stringToBitblastMode(std::string option, std::string optarg) throw(OptionException);
  virtual theory::bv::BvSlicerMode stringToBvSlicerMode(std::string option, std::string optarg) throw(OptionException);
  virtual void setBitblastAig(std::string option, bool arg) throw(OptionException);


  // theory/booleans/options_handlers.h
  virtual theory::booleans::BooleanTermConversionMode stringToBooleanTermConversionMode(std::string option, std::string optarg) throw(OptionException);

  // theory/uf/options_handlers.h
  virtual theory::uf::UfssMode stringToUfssMode(std::string option, std::string optarg) throw(OptionException);

  // theory/options_handlers.h
  virtual theory::TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg);
  virtual void useTheory(std::string option, std::string optarg);


  // printer/options_handlers.h
  virtual ModelFormatMode stringToModelFormatMode(std::string option, std::string optarg) throw(OptionException);
  virtual InstFormatMode stringToInstFormatMode(std::string option, std::string optarg) throw(OptionException);

  // decision/options_handlers.h
  virtual decision::DecisionMode stringToDecisionMode(std::string option, std::string optarg) throw(OptionException);
  virtual decision::DecisionWeightInternal stringToDecisionWeightInternal(std::string option, std::string optarg) throw(OptionException);


  // smt/options_handlers.h
  virtual void dumpMode(std::string option, std::string optarg);
  virtual LogicInfo* stringToLogicInfo(std::string option, std::string optarg) throw(OptionException);
  virtual SimplificationMode stringToSimplificationMode(std::string option, std::string optarg) throw(OptionException);
  virtual void beforeSearch(std::string option, bool value) throw(ModalException);
  virtual void setProduceAssertions(std::string option, bool value) throw();
  virtual void proofEnabledBuild(std::string option, bool value) throw(OptionException);
  virtual void dumpToFile(std::string option, std::string optarg);
  virtual void setRegularOutputChannel(std::string option, std::string optarg);
  virtual void setDiagnosticOutputChannel(std::string option, std::string optarg);
  virtual std::string checkReplayFilename(std::string option, std::string optarg);
  virtual std::ostream* checkReplayLogFilename(std::string option, std::string optarg);
  virtual void statsEnabledBuild(std::string option, bool value) throw(OptionException);
  virtual unsigned long tlimitHandler(std::string option, std::string optarg) throw(OptionException);
  virtual unsigned long tlimitPerHandler(std::string option, std::string optarg) throw(OptionException);
  virtual unsigned long rlimitHandler(std::string option, std::string optarg) throw(OptionException);
  virtual unsigned long rlimitPerHandler(std::string option, std::string optarg) throw(OptionException);

  /* expr/options_handlers.h */
  virtual void setDefaultExprDepth(std::string option, int depth);
  virtual void setDefaultDagThresh(std::string option, int dag);
  virtual void setPrintExprTypes(std::string option);

  /* main/options_handlers.h */
  virtual void showConfiguration(std::string option);
  virtual void showDebugTags(std::string option);
  virtual void showTraceTags(std::string option);
  virtual void threadN(std::string option);

  /* options/base_options_handlers.h */
  virtual void setVerbosity(std::string option, int value) throw(OptionException);
  virtual void increaseVerbosity(std::string option);
  virtual void decreaseVerbosity(std::string option);
  virtual OutputLanguage stringToOutputLanguage(std::string option, std::string optarg) throw(OptionException);
  virtual InputLanguage stringToInputLanguage(std::string option, std::string optarg) throw(OptionException) ;
  virtual void addTraceTag(std::string option, std::string optarg);
  virtual void addDebugTag(std::string option, std::string optarg);
  virtual void setPrintSuccess(std::string option, bool value);

private:
  SmtEngine* d_smtEngine;

  static std::string suggestTags(char const* const* validTags, std::string inputTag,
                                 char const* const* additionalTags = NULL);
  static std::string __cvc4_errno_failreason();

  /* Help strings */
  static const std::string s_decisionModeHelp;
  static const std::string s_simplificationHelp;
  static const std::string s_dumpHelp;
  static const std::string s_modelFormatHelp;
  static const std::string s_instFormatHelp ;
  static const std::string s_theoryOfModeHelp;
  static const std::string s_booleanTermConversionModeHelp;
  static const std::string s_ufssModeHelp;
  static const std::string s_bitblastingModeHelp;
  static const std::string s_bvSlicerModeHelp;

}; /* class SmtOptionsHandler */


}/* CVC4::smt namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SMT__SMT_OPTIONS_HANDLER_H */
