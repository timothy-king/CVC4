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

#include "base/modal_exception.h"
#include "options/option_exception.h"
#include "options/options_handler_interface.h"

namespace CVC4 {
namespace options {

void dumpMode(std::string option, std::string optarg, OptionsHandler* handler) {
  handler->dumpMode(option, optarg);
}

LogicInfo* stringToLogicInfo(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException){
  return handler->stringToLogicInfo(option, optarg);
}

SimplificationMode stringToSimplificationMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException){
  return handler->stringToSimplificationMode(option, optarg);
}

// ensure we haven't started search yet
void beforeSearch(std::string option, bool value, OptionsHandler* handler) throw(ModalException){
  handler->beforeSearch(option, value);
}

void setProduceAssertions(std::string option, bool value, OptionsHandler* handler) throw() {
  handler->setProduceAssertions(option, value);
}

// ensure we are a proof-enabled build of CVC4
void proofEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  handler->proofEnabledBuild(option, value);  
}

void dumpToFile(std::string option, std::string optarg, OptionsHandler* handler) {
  handler->dumpToFile(option, optarg);  
}

void setRegularOutputChannel(std::string option, std::string optarg, OptionsHandler* handler) {
  handler->setRegularOutputChannel(option, optarg);
}

void setDiagnosticOutputChannel(std::string option, std::string optarg, OptionsHandler* handler) {
  handler->setDiagnosticOutputChannel(option, optarg);
}

std::string checkReplayFilename(std::string option, std::string optarg, OptionsHandler* handler) {
  return handler->checkReplayFilename(option, optarg);
}

std::ostream* checkReplayLogFilename(std::string option, std::string optarg, OptionsHandler* handler) {
  return handler->checkReplayLogFilename(option, optarg);
}

// ensure we are a stats-enabled build of CVC4
void statsEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  return handler->statsEnabledBuild(option, value);
}

unsigned long tlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  return handler->tlimitHandler(option, optarg);
}

unsigned long tlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  return handler-> tlimitPerHandler(option, optarg);
}

unsigned long rlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  return handler->rlimitHandler(option, optarg);
}

unsigned long rlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  return handler->rlimitPerHandler(option, optarg);
}


}/* CVC4::options namespace */
}/* CVC4 namespace */
