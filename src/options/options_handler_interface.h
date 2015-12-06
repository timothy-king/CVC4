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

#ifndef __CVC4__OPTIONS__OPTIONS_HANDLER_INTERFACE_H
#define __CVC4__OPTIONS__OPTIONS_HANDLER_INTERFACE_H

#include <ostream>
#include <string>

#include "base/decision_mode.h"
#include "base/language.h"
#include "base/modal_exception.h"
#include "base/option_exception.h"
#include "base/printer_modes.h"
#include "base/simplification_mode.h"
#include "base/theoryof_mode.h"

namespace CVC4 {
class CVC4_PUBLIC LogicInfo;
}/* CVC4 namespace */

namespace CVC4 {
namespace options {

class CVC4_PUBLIC OptionsHandler {
public:
  virtual ~OptionsHandler() {}

  // DONE
  // decision/options_handlers.h
  // expr/options_handlers.h
  // main/options_handlers.h
  // options/base_options_handlers.h
  // printer/options_handlers.h
  // smt/options_handlers.h
  // theory/options_handlers.h

  // TODO:
  // theory/arith/options_handlers.h            \
  // theory/booleans/options_handlers.h         \
  // theory/bv/options_handlers.h               \
  // theory/fp/options_handlers.h
  // theory/quantifiers/options_handlers.h      \
  // theory/sets/options_handlers.h             \
  // theory/uf/options_handlers.h               \


  // theory/uf/options_handlers.h
  virtual theory::uf::UfssMode stringToUfssMode(std::string option, std::string optarg) throw(OptionException) = 0;

  // theory/options_handlers.h
  virtual theory::TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg) = 0;
  virtual void useTheory(std::string option, std::string optarg) = 0;


  // printer/options_handlers.h
  virtual ModelFormatMode stringToModelFormatMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual InstFormatMode stringToInstFormatMode(std::string option, std::string optarg) throw(OptionException) = 0;

  // decision/options_handlers.h
  virtual decision::DecisionMode stringToDecisionMode(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual decision::DecisionWeightInternal stringToDecisionWeightInternal(std::string option, std::string optarg) throw(OptionException) = 0;


  /* smt/options_handlers.h */
  virtual void dumpMode(std::string option, std::string optarg) = 0;
  virtual LogicInfo* stringToLogicInfo(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual SimplificationMode stringToSimplificationMode(std::string option, std::string optarg) throw(OptionException) = 0;

  virtual void beforeSearch(std::string option, bool value) throw(ModalException) = 0;
  virtual void setProduceAssertions(std::string option, bool value) throw() = 0;
  virtual void proofEnabledBuild(std::string option, bool value) throw(OptionException) = 0;
  virtual void dumpToFile(std::string option, std::string optarg) = 0;
  virtual void setRegularOutputChannel(std::string option, std::string optarg) = 0;
  virtual void setDiagnosticOutputChannel(std::string option, std::string optarg) = 0;
  virtual std::string checkReplayFilename(std::string option, std::string optarg) = 0;
  virtual std::ostream* checkReplayLogFilename(std::string option, std::string optarg) = 0;
  virtual void statsEnabledBuild(std::string option, bool value) throw(OptionException) = 0;
  virtual unsigned long tlimitHandler(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual unsigned long tlimitPerHandler(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual unsigned long rlimitHandler(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual unsigned long rlimitPerHandler(std::string option, std::string optarg) throw(OptionException) = 0;

  /* expr/options_handlers.h */
  virtual void setDefaultExprDepth(std::string option, int depth) = 0;
  virtual void setDefaultDagThresh(std::string option, int dag) = 0;
  virtual void setPrintExprTypes(std::string option) = 0;

  /* main/options_handlers.h */
  virtual void showConfiguration(std::string option) = 0;
  virtual void showDebugTags(std::string option) = 0;
  virtual void showTraceTags(std::string option) = 0;
  virtual void threadN(std::string option) = 0;

  /* options/base_options_handlers.h */
  virtual void setVerbosity(std::string option, int value) throw(OptionException) = 0;
  virtual void increaseVerbosity(std::string option) = 0;
  virtual void decreaseVerbosity(std::string option) = 0;
  virtual OutputLanguage stringToOutputLanguage(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual InputLanguage stringToInputLanguage(std::string option, std::string optarg) throw(OptionException) = 0;
  virtual void addTraceTag(std::string option, std::string optarg) = 0;
  virtual void addDebugTag(std::string option, std::string optarg) = 0;
  virtual void setPrintSuccess(std::string option, bool value) = 0;
}; /* class CVC4_PUBLIC OptionHandler */

// theory/uf/options_handlers.h
theory::uf::UfssMode stringToUfssMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);


// theory/options_handlers.h
theory::TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg, OptionsHandler* handler);
void useTheory(std::string option, std::string optarg, OptionsHandler* handler);

// printer/options_handlers.h
ModelFormatMode stringToModelFormatMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);
InstFormatMode stringToInstFormatMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);

// decision/options_handlers.h
decision::DecisionMode stringToDecisionMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);
decision::DecisionWeightInternal stringToDecisionWeightInternal(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);


/* options/base_options_handlers.h */
void setVerbosity(std::string option, int value, OptionsHandler* handler) throw(OptionException);
void increaseVerbosity(std::string option, OptionsHandler* handler);
void decreaseVerbosity(std::string option, OptionsHandler* handler);
OutputLanguage stringToOutputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);
InputLanguage stringToInputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);
void addTraceTag(std::string option, std::string optarg, OptionsHandler* handler);
void addDebugTag(std::string option, std::string optarg, OptionsHandler* handler);
void setPrintSuccess(std::string option, bool value, OptionsHandler* handler);

/* main/options_handlers.h */
void showConfiguration(std::string option, OptionsHandler* handler);
void showDebugTags(std::string option, OptionsHandler* handler);
void showTraceTags(std::string option, OptionsHandler* handler);
void threadN(std::string option, OptionsHandler* handler);

/* expr/options_handlers.h */
void setDefaultExprDepth(std::string option, int depth, OptionsHandler* handler);
void setDefaultDagThresh(std::string option, int dag, OptionsHandler* handler);
void setPrintExprTypes(std::string option, OptionsHandler* handler);

/* smt/options_handlers.h */
void dumpMode(std::string option, std::string optarg, OptionsHandler* handler);

LogicInfo* stringToLogicInfo(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);

SimplificationMode stringToSimplificationMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);

// ensure we haven't started search yet
void beforeSearch(std::string option, bool value, OptionsHandler* handler) throw(ModalException);

void setProduceAssertions(std::string option, bool value, OptionsHandler* handler) throw();

// ensure we are a proof-enabled build of CVC4
void proofEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException);

void dumpToFile(std::string option, std::string optarg, OptionsHandler* handler);

void setRegularOutputChannel(std::string option, std::string optarg, OptionsHandler* handler);

void setDiagnosticOutputChannel(std::string option, std::string optarg, OptionsHandler* handler);

std::string checkReplayFilename(std::string option, std::string optarg, OptionsHandler* handler);

std::ostream* checkReplayLogFilename(std::string option, std::string optarg, OptionsHandler* handler);

// ensure we are a stats-enabled build of CVC4
void statsEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException);

unsigned long tlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);

unsigned long tlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);

unsigned long rlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);

unsigned long rlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException);


}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* __CVC4__SMT__OPTIONS_HANDLERS_H */
