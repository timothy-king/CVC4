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
  Assert(ei.getViolated()->satisfiedBy(d_variables.getAssignment(v)));
  if(ei.isRelaxed()){
    Constraint viol = ei.getViolated();
    if(ei.sgn() > 0){
      d_variables.setLowerBoundConstraint(viol);
    }else{
      d_variables.setUpperBoundConstraint(viol);
    }
    ei.setUnrelaxed();
  }
  if(ei.inFocus()){
    d_focus.erase(ei.getHandle());
  }
  d_errInfo.remove(v);
}


void ErrorSet::transitionVariableIntoError(ArithVar v) {
  Assert(!inconsistent(v));
  int sgn = d_variables.strictlyBelowUpperBound(v) ? 1 : -1;
  Constraint c = (sgn == 1) ?
    d_variables.getLowerBoundConstraint(v) : d_variables.getUpperBoundConstraint(v);
  d_errInfo.set(v,ErrorInformation(v, c, sgn));
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
    if(inconsistent(back)){
      const ErrorInformation& ei = d_errInfo[back];
      if(ei.inFocus()){
        d_focus.update(ei.getHandle());
      }
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


// ArithVar ErrorSet::dequeueInconsistentBasicVariable(){
//   AlwaysAssert(!inCollectionMode());

//   Debug("arith_update") << "dequeueInconsistentBasicVariable()" << endl;

//   if(inDifferenceMode()){
//     while(!d_diffQueue.empty()){
//       ArithVar var = d_diffQueue.front().variable();
//       switch(d_pivotRule){
//       case MINIMUM:
//         pop_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::minimumRule);
//         break;
//       case BREAK_TIES:
//         pop_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::breakTiesRules);
//         break;
//       case MAXIMUM:
//         pop_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::maximumRule);
//         break;
//       }
//       d_diffQueue.pop_back();
//       Debug("arith_update") << "possiblyInconsistentGriggio var" << var << endl;
//       if(basicAndInconsistent(var)){
//         return var;
//       }
//     }
//   }else{
//     Assert(inVariableOrderMode());
//     Debug("arith_update") << "possiblyInconsistent.size()"
//                           << d_varOrderQueue.size() << endl;

//     while(!d_varOrderQueue.empty()){
//       ArithVar var = d_varOrderQueue.front();
//       pop_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
//       d_varOrderQueue.pop_back();

//       d_varSet.remove(var);

//       Debug("arith_update") << "possiblyInconsistent var" << var << endl;
//       if(basicAndInconsistent(var)){
//         return var;
//       }
//     }
//   }
//   return ARITHVAR_SENTINEL;
// }

DeltaRational ErrorSet::computeDiff(ArithVar v) const{
  Assert(inconsistent(v));
  const DeltaRational& beta = d_variables.getAssignment(v);
  DeltaRational diff = d_variables.cmpAssignmentLowerBound(v) < 0 ?
    d_variables.getLowerBound(v) - beta:
    beta - d_variables.getUpperBound(v);

  Assert(diff.sgn() > 0);
  return diff;
}

// void ErrorSet::enqueueIfInconsistent(ArithVar basic){
//   Assert(d_tableau.isBasic(basic));

//   if(basicAndInconsistent(basic)){
//     ++d_statistics.d_enqueues;

//     switch(d_modeInUse){
//     case Collection:
//       ++d_statistics.d_enqueuesCollection;
//       if(!d_varSet.isMember(basic)){
//         d_varSet.add(basic);
//         d_candidates.push_back(basic);
//       }else{
//         ++d_statistics.d_enqueuesCollectionDuplicates;
//       }
//       break;
//     case VariableOrder:
//       ++d_statistics.d_enqueuesVarOrderMode;
//       if(!d_varSet.isMember(basic)){
//         d_varSet.add(basic);
//         d_varOrderQueue.push_back(basic);
//         push_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
//       }else{
//         ++d_statistics.d_enqueuesVarOrderModeDuplicates;
//       }
//       break;
//     case Difference:
//       ++d_statistics.d_enqueuesDiffMode;
//       d_diffQueue.push_back(computeDiff(basic));
//       switch(d_pivotRule){
//       case MINIMUM:
//         push_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::minimumRule);
//         break;
//       case BREAK_TIES:
//         push_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::breakTiesRules);
//         break;
//       case MAXIMUM:
//         push_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::maximumRule);
//         break;
//       }
//       break;
//     default:
//       Unreachable();
//     }
//   }
// }

// void ErrorSet::transitionToDifferenceMode() {
//   Assert(inCollectionMode());
//   Assert(d_varOrderQueue.empty());
//   Assert(d_diffQueue.empty());

//   Debug("arith::priorityqueue") << "transitionToDifferenceMode()" << endl;
//   d_varSet.purge();

//   ArithVarArray::const_iterator i = d_candidates.begin(), end = d_candidates.end();
//   for(; i != end; ++i){
//     ArithVar var = *i;
//     if(basicAndInconsistent(var)){
//       d_diffQueue.push_back(computeDiff(var));
//     }
//   }

//   switch(d_pivotRule){
//   case MINIMUM:
//     Debug("arith::pivotRule") << "Making the minimum heap." << endl;
//     make_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::minimumRule);
//     break;
//   case BREAK_TIES:
//     Debug("arith::pivotRule") << "Making the break ties heap." << endl;
//     make_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::breakTiesRules);
//     break;
//   case MAXIMUM:
//     Debug("arith::pivotRule") << "Making the maximum heap." << endl;
//     make_heap(d_diffQueue.begin(), d_diffQueue.end(), VarDRatPair::maximumRule);
//     break;
//   }

//   d_candidates.clear();
//   d_modeInUse = Difference;

//   Assert(d_varSet.empty());
//   Assert(inDifferenceMode());
//   Assert(d_varOrderQueue.empty());
//   Assert(d_candidates.empty());
// }

// void ErrorSet::transitionToVariableOrderMode() {
//   Assert(inDifferenceMode());
//   Assert(d_varOrderQueue.empty());
//   Assert(d_candidates.empty());
//   Assert(d_varSet.empty());

//   Debug("arith::priorityqueue") << "transitionToVariableOrderMode()" << endl;

//   DifferenceArray::const_iterator i = d_diffQueue.begin(), end = d_diffQueue.end();
//   for(; i != end; ++i){
//     ArithVar var = (*i).variable();
//     if(basicAndInconsistent(var) && !d_varSet.isMember(var)){
//       d_varSet.add(var);
//       d_varOrderQueue.push_back(var);
//     }
//   }
//   make_heap(d_varOrderQueue.begin(), d_varOrderQueue.end(), std::greater<ArithVar>());
//   d_diffQueue.clear();
//   d_modeInUse = VariableOrder;

//   Assert(inVariableOrderMode());
//   Assert(d_diffQueue.empty());
//   Assert(d_candidates.empty());
// }

// void ErrorSet::transitionToCollectionMode() {
//   Assert(inDifferenceMode() || inVariableOrderMode());
//   Assert(d_candidates.empty());

//   if(inDifferenceMode()){
//     Assert(d_varSet.empty());
//     Assert(d_varOrderQueue.empty());
//     Assert(inDifferenceMode());

//     DifferenceArray::const_iterator i = d_diffQueue.begin(), end = d_diffQueue.end();
//     for(; i != end; ++i){
//       ArithVar var = (*i).variable();
//       if(basicAndInconsistent(var) && !d_varSet.isMember(var)){
//         d_candidates.push_back(var);
//         d_varSet.add(var);
//       }
//     }
//     d_diffQueue.clear();
//   }else{
//     Assert(d_diffQueue.empty());
//     Assert(inVariableOrderMode());

//     d_varSet.purge();

//     ArithVarArray::const_iterator i = d_varOrderQueue.begin(), end = d_varOrderQueue.end();
//     for(; i != end; ++i){
//       ArithVar var = *i;
//       if(basicAndInconsistent(var)){
//         d_candidates.push_back(var);
//         d_varSet.add(var); // cannot have duplicates.
//       }
//     }
//     d_varOrderQueue.clear();
//   }

//   Assert(d_diffQueue.empty());
//   Assert(d_varOrderQueue.empty());

//   Debug("arith::priorityqueue") << "transitionToCollectionMode()" << endl;

//   d_modeInUse = Collection;
// }

// void ErrorSet::clear(){
//   switch(d_modeInUse){
//   case Collection:
//     d_candidates.clear();
//     d_varSet.purge();
//     break;
//   case VariableOrder:
//     if(!d_varOrderQueue.empty()) {
//       d_varOrderQueue.clear();
//       d_varSet.purge();
//     }
//     break;
//   case Difference:
//     if(!d_diffQueue.empty()){
//       d_diffQueue.clear();
//       d_varSet.purge();
//     }
//     break;
//   default:
//     Unreachable();
//   }

//   Assert(d_varSet.empty());
//   Assert(d_candidates.empty());
//   Assert(d_varOrderQueue.empty());
//   Assert(d_diffQueue.empty());
// }

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
