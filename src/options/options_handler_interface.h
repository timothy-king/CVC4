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

#include "base/modal_exception.h"
#include "base/simplification_mode.h"
#include "options/option_exception.h"

namespace CVC4 {
class CVC4_PUBLIC LogicInfo;
}/* CVC4 namespace */

namespace CVC4 {
namespace options {

class CVC4_PUBLIC OptionsHandler {
public:
  virtual ~OptionsHandler() {}

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
  
}; /* class CVC4_PUBLIC OptionHandler */


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
