/*********************                                                        */
/*! \file arith_priority_queue.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/error_set.h"
#include "theory/arith/constraint.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {



ErrorSet::Statistics::Statistics():
  d_enqueues("theory::arith::pqueue::enqueues", 0),
  d_enqueuesCollection("theory::arith::pqueue::enqueuesCollection", 0),
  d_enqueuesDiffMode("theory::arith::pqueue::enqueuesDiffMode", 0),
  d_enqueuesVarOrderMode("theory::arith::pqueue::enqueuesVarOrderMode", 0),
  d_enqueuesCollectionDuplicates("theory::arith::pqueue::enqueuesCollectionDuplicates", 0),
  d_enqueuesVarOrderModeDuplicates("theory::arith::pqueue::enqueuesVarOrderModeDuplicates", 0)
{
  StatisticsRegistry::registerStat(&d_enqueues);
  StatisticsRegistry::registerStat(&d_enqueuesCollection);
  StatisticsRegistry::registerStat(&d_enqueuesDiffMode);
  StatisticsRegistry::registerStat(&d_enqueuesVarOrderMode);
  StatisticsRegistry::registerStat(&d_enqueuesCollectionDuplicates);
  StatisticsRegistry::registerStat(&d_enqueuesVarOrderModeDuplicates);
}

ErrorSet::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_enqueues);
  StatisticsRegistry::unregisterStat(&d_enqueuesCollection);
  StatisticsRegistry::unregisterStat(&d_enqueuesDiffMode);
  StatisticsRegistry::unregisterStat(&d_enqueuesVarOrderMode);
  StatisticsRegistry::unregisterStat(&d_enqueuesCollectionDuplicates);
  StatisticsRegistry::unregisterStat(&d_enqueuesVarOrderModeDuplicates);
}

ErrorSet::ErrorSet(ArithVariables& vars):
  d_variables(vars),
  d_errInfo(),
  d_focus(ComparatorPivotRule(&d_errInfo, VAR_ORDER)),
  d_outOfFocus(),
  d_signals()
{}

ErrorSelectionRule ErrorSet::getSelectionRule() const{
  return d_focus.value_comp().getRule();
}

void ErrorSet::recomputeAmount(ErrorInformation& ei){
  switch(getSelectionRule()){
  case MINIMUM_AMOUNT:
  case MAXIMUM_AMOUNT:
    ei.setAmount(computeDiff(ei.getVariable()));
    break;
  case  VAR_ORDER:
    //do nothing
    break;
  }
}

void ErrorSet::setSelectionRule(ErrorSelectionRule rule){
  if(rule != getSelectionRule()){
    ErrorSetHeap into(ComparatorPivotRule(&d_errInfo, rule));
    ErrorSetHeap::iterator iter = d_focus.begin();
    ErrorSetHeap::iterator i_end = d_focus.end();
    for(; iter != i_end; ++iter){
      ArithVar v = *iter;
      ErrorInformation& ei = d_errInfo.get(v);
      if(ei.inFocus()){
        recomputeAmount(ei);
        ErrorSetHandle handle = into.push(v);
        ei.setHandle(handle);
      }
    }
    d_focus.swap(into);
  }
}

ComparatorPivotRule::ComparatorPivotRule(const ErrorInfoMap* es, ErrorSelectionRule r):
  d_errInfo(es), d_rule (r)
{}

bool ComparatorPivotRule::operator()(ArithVar v, ArithVar u) const {
  switch(d_rule){
  case VAR_ORDER:
    return v < u;
  case MINIMUM_AMOUNT:
    {
      const DeltaRational& vamt = (*d_errInfo)[v].getAmount();
      const DeltaRational& uamt = (*d_errInfo)[u].getAmount();
      int cmp = vamt.cmp(uamt);
      if(cmp == 0){
        return v < u;
      }else{
        return cmp < 0;
      }
    }
  case MAXIMUM_AMOUNT:
    {
      const DeltaRational& vamt = (*d_errInfo)[v].getAmount();
      const DeltaRational& uamt = (*d_errInfo)[u].getAmount();
      int cmp = vamt.cmp(uamt);
      if(cmp == 0){
        return v < u;
      }else{
        return cmp > 0;
      }
    }
  default:
    Unreachable();
  }
}

void ErrorSet::update(ErrorInformation& ei){
  if(ei.inFocus()){

    switch(getSelectionRule()){
    case MINIMUM_AMOUNT:
    case MAXIMUM_AMOUNT:
      ei.setAmount(computeDiff(ei.getVariable()));
      d_focus.update(ei.getHandle());
      break;
    case  VAR_ORDER:
      //do nothing
      break;
    }
  }
}

/** A variable becomes satisfied. */
void ErrorSet::transitionVariableOutOfError(ArithVar v) {
  Assert(!inconsistent(v));
  ErrorInformation& ei = d_errInfo.get(v);
  Assert(ei.debugInitialized());
  if(ei.isRelaxed()){
    Constraint viol = ei.getViolated();
    if(ei.sgn() > 0){
      d_variables.setLowerBoundConstraint(viol);
    }else{
      d_variables.setUpperBoundConstraint(viol);
    }
    Assert(!inconsistent(v));
    ei.setUnrelaxed();
  }
  if(ei.inFocus()){
    d_focus.erase(ei.getHandle());
  }
  d_errInfo.remove(v);
}


void ErrorSet::transitionVariableIntoError(ArithVar v) {
  Assert(inconsistent(v));
  bool vilb = d_variables.cmpAssignmentLowerBound(v) < 0;
  int sgn = vilb ? 1 : -1;
  Constraint c = vilb ?
    d_variables.getLowerBoundConstraint(v) : d_variables.getUpperBoundConstraint(v);
  d_errInfo.set(v, ErrorInformation(v, c, sgn));
  ErrorInformation& ei = d_errInfo.get(v);

  switch(getSelectionRule()){
  case MINIMUM_AMOUNT:
  case MAXIMUM_AMOUNT:
    ei.setAmount(computeDiff(v));
    break;
  case  VAR_ORDER:
    //do nothing
    break;
  }
  ei.setInFocus(true);
  ErrorSetHandle handle = d_focus.push(v);
  ei.setHandle(handle);
}

void ErrorSet::dropFromFocus(ArithVar v) {
  Assert(inError(v));
  ErrorInformation& ei = d_errInfo.get(v);
  Assert(ei.inFocus());
  d_focus.erase(ei.getHandle());
  ei.setInFocus(false);
  d_outOfFocus.push_back(v);
}

void ErrorSet::addBackIntoFocus(ArithVar v) {
  Assert(inError(v));
  ErrorInformation& ei = d_errInfo.get(v);
  Assert(!ei.inFocus());
  switch(getSelectionRule()){
  case MINIMUM_AMOUNT:
  case MAXIMUM_AMOUNT:
    ei.setAmount(computeDiff(v));
    break;
  case  VAR_ORDER:
    //do nothing
    break;
  }
    
  ei.setInFocus(true);
  ErrorSetHandle handle = d_focus.push(v);
  ei.setHandle(handle);
}

void ErrorSet::blur(){
  while(!d_outOfFocus.empty()){
    ArithVar v = d_outOfFocus.back();
    d_outOfFocus.pop_back();

    if(inError(v)){
      addBackIntoFocus(v);
    }
  }
}



void ErrorSet::popSignal() {
  ArithVar back = d_signals.back();
  d_signals.pop_back();

  if(inError(back)){
    bool vilb = d_variables.cmpAssignmentLowerBound(back) < 0;
    bool viub = d_variables.cmpAssignmentUpperBound(back) > 0;
    if(vilb || viub){
      ErrorInformation& ei = d_errInfo.get(back);
      Constraint curr = vilb ?  d_variables.getLowerBoundConstraint(back)
        : d_variables.getUpperBoundConstraint(back);
      if(curr != ei.getViolated()){
        ei.reset(curr, vilb ? 1 : -1);
      }
      update(ei);
    }else{
      transitionVariableOutOfError(back);
    }
  }else if(inconsistent(back)){
    transitionVariableIntoError(back);
  }
}

void ErrorSet::clear(){
  // Nothing should be relaxed!
  d_signals.clear();
  d_errInfo.clear();
  d_focus.clear();
}

void ErrorSet::reduce(){
  Assert(d_nowConsistent.empty());
  for(error_iterator ei=errorBegin(), ei_end=errorEnd(); ei != ei_end; ++ei){
    ArithVar curr = *ei;
    if(!inconsistent(curr)){
      d_nowConsistent.push_back(curr);
    }
  }
  while(!d_nowConsistent.empty()){
    ArithVar back = d_nowConsistent.back();
    d_nowConsistent.pop_back();
    transitionVariableOutOfError(back);
  }
  Assert(d_nowConsistent.empty());
}

DeltaRational ErrorSet::computeDiff(ArithVar v) const{
  Assert(inconsistent(v));
  const DeltaRational& beta = d_variables.getAssignment(v);
  DeltaRational diff = d_variables.cmpAssignmentLowerBound(v) < 0 ?
    d_variables.getLowerBound(v) - beta:
    beta - d_variables.getUpperBound(v);

  Assert(diff.sgn() > 0);
  return diff;
}

ostream& operator<<(ostream& out, ErrorSelectionRule rule) {
  switch(rule) {
  case VAR_ORDER:
    out << "VAR_ORDER";
    break;
  case MINIMUM_AMOUNT:
    out << "MINIMUM_AMOUNT";
    break;
  case MAXIMUM_AMOUNT:
    out << "MAXIMUM_AMOUNT";
    break;
  default:
    out << "PivotRule!UNKNOWN";
  }

  return out;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
