/*********************                                                        */
/*! \file simplex.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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


#include "theory/arith/simplex.h"
#include "theory/arith/options.h"
#include "theory/arith/constraint.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

SimplexDecisionProcedure::SimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : d_conflictVariables()
  , d_linEq(linEq)
  , d_variables(d_linEq.getVariables())
  , d_tableau(d_linEq.getTableau())
  , d_errorSet(errors)
  , d_numVariables(0)
  , d_conflictChannel(conflictChannel)
  , d_arithVarMalloc(tvmalloc)
  , d_errorSize(0)
  , d_focusSize(0)
  , d_focusErrorVar(ARITHVAR_SENTINEL)
  , d_focusCoefficients()
  , d_zero(0)
{
  d_heuristicRule = options::arithErrorSelectionRule();
  d_errorSet.setSelectionRule(d_heuristicRule);
}

bool SimplexDecisionProcedure::standardProcessSignals(TimerStat &timer, IntStat& conflicts) {
  TimerStat::CodeTimer codeTimer(timer);
  Assert( d_conflictVariables.empty() );


  while(d_errorSet.moreSignals()){
    ArithVar curr = d_errorSet.topSignal();
    if(d_tableau.isBasic(curr) && !d_variables.assignmentIsConsistent(curr)){
      Assert(d_linEq.basicIsTracked(curr));

      if(!d_conflictVariables.isMember(curr) && checkBasicForConflict(curr)){

        Debug("recentlyViolated")
          << "It worked? "
          << conflicts.getData()
          << " " << curr
          << " "  << checkBasicForConflict(curr) << endl;
        reportConflict(curr);
        ++conflicts;
      }
    }
    // Pop signal afterwards in case d_linEq.trackVariable(curr);
    // is needed for for the ErrorSet
    d_errorSet.popSignal();
  }

  d_errorSize = d_errorSet.errorSize();
  d_focusSize = d_errorSet.focusSize();

  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
}

/** Reports a conflict to on the output channel. */
void SimplexDecisionProcedure::reportConflict(ArithVar basic){
  Assert(!d_conflictVariables.isMember(basic));
  Assert(checkBasicForConflict(basic));
  Node conflict = generatConflictForBasic(basic);

  static bool verbose = false;
  if(verbose) { Message() << "conflict " << basic << " " << conflict << endl; }
  Assert(!conflict.isNull());
  d_conflictChannel(conflict);
  d_conflictVariables.add(basic);
}

Node SimplexDecisionProcedure::generatConflictForBasic(ArithVar basic) const {

  Assert(d_tableau.isBasic(basic));
  Assert(checkBasicForConflict(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    Assert(d_linEq.nonbasicsAtUpperBounds(basic));
    return d_linEq.generateConflictBelowLowerBound(basic);
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    Assert(d_linEq.nonbasicsAtLowerBounds(basic));
    return d_linEq.generateConflictAboveUpperBound(basic);
  }else{
    Unreachable();
  }
}
Node SimplexDecisionProcedure::maybeGenerateConflictForBasic(ArithVar basic) const {
  if(checkBasicForConflict(basic)){
    return generatConflictForBasic(basic);
  }else{
    return Node::null();
  }
}

bool SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic) const {
  Assert(d_tableau.isBasic(basic));
  Assert(d_linEq.basicIsTracked(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    if(d_linEq.nonbasicsAtUpperBounds(basic)){
      return true;
    }
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    if(d_linEq.nonbasicsAtLowerBounds(basic)){
      return true;
    }
  }
  return false;
}

void SimplexDecisionProcedure::tearDownFocusErrorFunction(TimerStat& timer){
  TimerStat::CodeTimer codeTimer(timer);
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  d_tableau.removeBasicRow(d_focusErrorVar);
  releaseVariable(d_focusErrorVar);

  d_focusErrorVar = ARITHVAR_SENTINEL;

  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
}

void SimplexDecisionProcedure::shrinkFocusFunction(TimerStat& timer, const ArithVarVec& dropped){
  TimerStat::CodeTimer codeTimer(timer);
  for(ArithVarVec::const_iterator i=dropped.begin(), i_end = dropped.end(); i != i_end; ++i){
    ArithVar back = *i;

    int focusSgn = d_errorSet.focusSgn(back);
    Rational chg(-focusSgn);

    d_linEq.substitutePlusTimesConstant(d_focusErrorVar, back, chg);
  }
}
void SimplexDecisionProcedure::adjustFocusFunction(TimerStat& timer, const AVIntPairVec& focusChanges){
  TimerStat::CodeTimer codeTimer(timer);
  int oldBasicSgnChange = 0;
  int newBasicSgnChange = 0;
  for(AVIntPairVec::const_iterator i=focusChanges.begin(), i_end = focusChanges.end(); i != i_end; ++i){
    ArithVar v = (*i).first;
    int focusChange = (*i).second;

    Rational chg(focusChange);
    if(d_tableau.isBasic(v)){
      d_linEq.substitutePlusTimesConstant(d_focusErrorVar, v, chg);
    }else{
      d_linEq.directlyAddToCoefficient(d_focusErrorVar, v, chg);
    }
  }
}

void SimplexDecisionProcedure::constructFocusErrorFunction(TimerStat& timer){
  TimerStat::CodeTimer codeTimer(timer);
  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
  Assert(!d_errorSet.focusEmpty());
  d_focusErrorVar = requestVariable();


  std::vector<Rational> coeffs;
  std::vector<ArithVar> variables;

  for(ErrorSet::focus_iterator iter = d_errorSet.focusBegin(), end = d_errorSet.focusEnd(); iter != end; ++iter){
    ArithVar e = *iter;

    Assert(d_tableau.isBasic(e));
    Assert(!d_variables.assignmentIsConsistent(e));

    int sgn = d_errorSet.getSgn(e);
    coeffs.push_back(Rational(sgn));
    variables.push_back(e);
  }
  d_tableau.addRow(d_focusErrorVar, coeffs, variables);
  DeltaRational newAssignment = d_linEq.computeRowValue(d_focusErrorVar, false);
  d_variables.setAssignment(d_focusErrorVar, newAssignment);

  d_linEq.trackVariable(d_focusErrorVar);

  Debug("pu") << d_focusErrorVar << " " << newAssignment << endl;
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
}


void SimplexDecisionProcedure::loadFocusSigns(){
  Assert(d_focusCoefficients.empty());
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(d_focusErrorVar); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    d_focusCoefficients.set(curr, &e.getCoefficient());
  }
}

void SimplexDecisionProcedure::unloadFocusSigns(){
  d_focusCoefficients.purge();
}

const Rational& SimplexDecisionProcedure::focusCoefficient(ArithVar nb) const {
  if(d_focusCoefficients.isKey(nb)){
    return *(d_focusCoefficients[nb]);
  }else{
    return d_zero;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
