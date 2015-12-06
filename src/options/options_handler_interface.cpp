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

#include "base/language.h"
#include "base/modal_exception.h"
#include "base/option_exception.h"
#include "options/options_handler_interface.h"

namespace CVC4 {
namespace options {

/* options/base_options_handlers.h */
void setVerbosity(std::string option, int value, OptionsHandler* handler) throw(OptionException) {
  handler->setVerbosity(option, value);
}
void increaseVerbosity(std::string option, OptionsHandler* handler) {
  handler->increaseVerbosity(option);
}
void decreaseVerbosity(std::string option, OptionsHandler* handler) {
  handler->decreaseVerbosity(option);
}

OutputLanguage stringToOutputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  return handler->stringToOutputLanguage(option, optarg);
}

InputLanguage stringToInputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  return handler->stringToInputLanguage(option, optarg);
}
void addTraceTag(std::string option, std::string optarg, OptionsHandler* handler);
void addDebugTag(std::string option, std::string optarg, OptionsHandler* handler);
void setPrintSuccess(std::string option, bool value, OptionsHandler* handler);


/* main/options_handlers.h */
void showConfiguration(std::string option, OptionsHandler* handler) {
  handler->showConfiguration(option);
}

void showDebugTags(std::string option, OptionsHandler* handler) {
  handler->showDebugTags(option);
}

void showTraceTags(std::string option, OptionsHandler* handler) {
  handler->showTraceTags(option);
}

void threadN(std::string option, OptionsHandler* handler){
  handler->threadN(option);
}

/* expr/options_handlers.h */
void setDefaultExprDepth(std::string option, int depth, OptionsHandler* handler){
  handler->setDefaultExprDepth(option, depth);
}

void setDefaultDagThresh(std::string option, int dag, OptionsHandler* handler){
  handler->setDefaultDagThresh(option, dag);
}

void setPrintExprTypes(std::string option, OptionsHandler* handler) {
  handler->setPrintExprTypes(option);
}


/* smt/options_handlers.h */
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
