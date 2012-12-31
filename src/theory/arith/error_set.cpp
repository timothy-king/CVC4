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


ErrorInformation::ErrorInformation()
  : d_variable(ARITHVAR_SENTINEL)
  , d_violated(NullConstraint)
  , d_sgn(0)
  , d_relaxed(false)
  , d_inFocus(false)
  , d_handle()
  , d_amount(NULL)
{
  Debug("arith::error::mem") << "def constructor " << d_variable << " "  << d_amount << endl;
}

ErrorInformation::ErrorInformation(ArithVar var, Constraint vio, int sgn)
  : d_variable(var)
  , d_violated(vio)
  , d_sgn(sgn)
  , d_relaxed(false)
  , d_inFocus(false)
  , d_handle()
  , d_amount(NULL)
{
  Assert(debugInitialized());
  Debug("arith::error::mem") << "constructor " << d_variable << " "  << d_amount << endl;
}


ErrorInformation::~ErrorInformation() {
  Assert(d_relaxed != true);
  if(d_amount != NULL){
    Debug("arith::error::mem") << d_amount << endl;
    Debug("arith::error::mem") << "destroy " << d_variable << " "  << d_amount << endl;
    delete d_amount;
    d_amount = NULL;
  }
}

ErrorInformation::ErrorInformation(const ErrorInformation& ei)
  : d_variable(ei.d_variable)
  , d_violated(ei.d_violated)
  , d_sgn(ei.d_sgn)
  , d_relaxed(ei.d_relaxed)
  , d_inFocus(ei.d_inFocus)
  , d_handle(ei.d_handle)
{
  if(ei.d_amount == NULL){
    d_amount = NULL;
  }else{
    d_amount = new DeltaRational(*ei.d_amount);
  }
  Debug("arith::error::mem") << "copy const " << d_variable << " "  << d_amount << endl;
}

ErrorInformation& ErrorInformation::operator=(const ErrorInformation& ei){
  d_variable = ei.d_variable;
  d_violated = ei.d_violated;
  d_sgn = ei.d_sgn;
  d_relaxed = (ei.d_relaxed);
  d_inFocus = (ei.d_inFocus);
  d_handle = (ei.d_handle);
  if(d_amount != NULL && ei.d_amount != NULL){
    Debug("arith::error::mem") << "assignment assign " << d_variable << " "  << d_amount << endl;
    *d_amount = *ei.d_amount;
  }else if(ei.d_amount != NULL){
    d_amount = new DeltaRational(*ei.d_amount);
    Debug("arith::error::mem") << "assignment alloc " << d_variable << " "  << d_amount << endl;
  }else if(d_amount != NULL){
    Debug("arith::error::mem") << "assignment release " << d_variable << " "  << d_amount << endl;
    delete d_amount;
    d_amount = NULL;
  }else{
    d_amount = NULL;
  }
  return *this;
}

void ErrorInformation::reset(Constraint c, int sgn){
  Assert(!isRelaxed());
  Assert(c != NullConstraint);
  d_violated = c;
  d_sgn = sgn;

  if(d_amount != NULL){
    delete d_amount;
    Debug("arith::error::mem") << "reset " << d_variable << " "  << d_amount << endl;
    d_amount = NULL;
  }
}

void ErrorInformation::setAmount(const DeltaRational& am){
  if(d_amount == NULL){
    d_amount = new DeltaRational;
    Debug("arith::error::mem") << "setAmount " << d_variable << " "  << d_amount << endl;
  }
  (*d_amount) = am;
}

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

ErrorSet::ErrorSet(ArithVariables& vars, TableauSizes tabSizes, BoundCountingLookup lookups):
  d_variables(vars),
  d_errInfo(),
  d_focus(ComparatorPivotRule(this, VAR_ORDER)),
  d_outOfFocus(),
  d_signals(),
  d_tableauSizes(tabSizes),
  d_boundLookup(lookups)
{}

ErrorSelectionRule ErrorSet::getSelectionRule() const{
  return d_focus.value_comp().getRule();
}

void ErrorSet::recomputeAmount(ErrorInformation& ei, ErrorSelectionRule rule){
  switch(rule){
  case MINIMUM_AMOUNT:
  case MAXIMUM_AMOUNT:
    ei.setAmount(computeDiff(ei.getVariable()));
    break;
  case SUM_METRIC:
  case VAR_ORDER:
    //do nothing
    break;
  }
}

void ErrorSet::setSelectionRule(ErrorSelectionRule rule){
  if(rule != getSelectionRule()){
    FocusSet into(ComparatorPivotRule(this, rule));
    FocusSet::const_iterator iter = d_focus.begin();
    FocusSet::const_iterator i_end = d_focus.end();
    for(; iter != i_end; ++iter){
      ArithVar v = *iter;
      ErrorInformation& ei = d_errInfo.get(v);
      if(ei.inFocus()){
        recomputeAmount(ei, rule);
        FocusSetHandle handle = into.push(v);
        ei.setHandle(handle);
      }
    }
    d_focus.swap(into);
  }
  Assert(getSelectionRule() == rule);
}

ComparatorPivotRule::ComparatorPivotRule(const ErrorSet* es, ErrorSelectionRule r):
  d_errorSet(es), d_rule (r)
{}

bool ComparatorPivotRule::operator()(ArithVar v, ArithVar u) const {
  switch(d_rule){
  case VAR_ORDER:
    // This needs to be the reverse of the minVariableOrder
    return v > u;
  case SUM_METRIC:
    {
      uint32_t v_metric = d_errorSet->sumMetric(v);
      uint32_t u_metric = d_errorSet->sumMetric(u);
      if(v_metric == u_metric){
        return v > u;
      }else{
        return v_metric > u_metric;
      }
    }
  case MINIMUM_AMOUNT:
    {
      const DeltaRational& vamt = d_errorSet->getAmount(v);
      const DeltaRational& uamt = d_errorSet->getAmount(u);
      int cmp = vamt.cmp(uamt);
      if(cmp == 0){
        return v > u;
      }else{
        return cmp > 0;
      }
    }
  case MAXIMUM_AMOUNT:
    {
      const DeltaRational& vamt = d_errorSet->getAmount(v);
      const DeltaRational& uamt = d_errorSet->getAmount(u);
      int cmp = vamt.cmp(uamt);
      if(cmp == 0){
        return v > u;
      }else{
        return cmp < 0;
      }
    }
  }
  Unreachable();
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
    case  SUM_METRIC:
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
    ei.setInFocus(false);
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
  case SUM_METRIC:
  case VAR_ORDER:
    //do nothing
    break;
  }
  ei.setInFocus(true);
  FocusSetHandle handle = d_focus.push(v);
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
  case SUM_METRIC:
  case VAR_ORDER:
    //do nothing
    break;
  }
    
  ei.setInFocus(true);
  FocusSetHandle handle = d_focus.push(v);
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
  d_errInfo.purge();
  d_focus.clear();
}

void ErrorSet::reduceToSignals(){
  for(error_iterator ei=errorBegin(), ei_end=errorEnd(); ei != ei_end; ++ei){
    ArithVar curr = *ei;
    signalVariable(curr);
  }
  
  d_errInfo.purge();
  d_focus.clear();
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
  case SUM_METRIC:
    out << "SUM_METRIC";
    break;
  }

  return out;
}

void ErrorSet::debugPrint() const {
  static int instance = 0;
  ++instance;
  Debug("error") << "error set debugprint " << instance << endl;
  for(error_iterator i = errorBegin(), i_end = errorEnd();
      i != i_end; ++i){
    ArithVar e = *i;
    const ErrorInformation& ei = d_errInfo[e];
    ei.print(Debug("error"));
  }
  Debug("error") << "focus ";
  for(focus_iterator i = focusBegin(), i_end = focusEnd();
      i != i_end; ++i){
    Debug("error") << *i << " ";
  }
  Debug("error") << ";" << endl;
}

void ErrorSet::focusDownToJust(ArithVar v) {
  for(ErrorSet::focus_iterator i =focusBegin(), i_end = focusEnd(); i != i_end; ++i){
    ArithVar f = *i;
    ErrorInformation& fei = d_errInfo.get(f);
    fei.setInFocus(false);
  }
  d_focus.clear();

  ErrorInformation& vei = d_errInfo.get(v);
  FocusSetHandle handle = d_focus.push(v);
  vei.setHandle(handle);
  vei.setInFocus(true);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
