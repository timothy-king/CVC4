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

  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
}

/** Reports a conflict to on the output channel. */
void SimplexDecisionProcedure::reportConflict(ArithVar basic){
  Assert(!d_conflictVariables.isMember(basic));
  Assert(checkBasicForConflict(basic));
  Node conflict = generateConflictForBasic(basic);

  static bool verbose = false;
  if(verbose) { Message() << "conflict " << basic << " " << conflict << endl; }
  Assert(!conflict.isNull());
  d_conflictChannel(conflict);
  d_conflictVariables.add(basic);
}

Node SimplexDecisionProcedure::generateConflictForBasic(ArithVar basic) const {

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
    return generateConflictForBasic(basic);
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

void SimplexDecisionProcedure::tearDownInfeasiblityFunction(TimerStat& timer, ArithVar tmp){
  TimerStat::CodeTimer codeTimer(timer);
  Assert(tmp != ARITHVAR_SENTINEL);
  Assert(d_tableau.isBasic(tmp));

  d_tableau.removeBasicRow(tmp);
  releaseVariable(tmp);
}

void SimplexDecisionProcedure::shrinkInfeasFunc(TimerStat& timer, ArithVar inf, const ArithVarVec& dropped){
  TimerStat::CodeTimer codeTimer(timer);
  for(ArithVarVec::const_iterator i=dropped.begin(), i_end = dropped.end(); i != i_end; ++i){
    ArithVar back = *i;

    int focusSgn = d_errorSet.focusSgn(back);
    Rational chg(-focusSgn);

    d_linEq.substitutePlusTimesConstant(inf, back, chg);
  }
}

void SimplexDecisionProcedure::adjustInfeasFunc(TimerStat& timer, ArithVar inf, const AVIntPairVec& focusChanges){
  TimerStat::CodeTimer codeTimer(timer);
  for(AVIntPairVec::const_iterator i=focusChanges.begin(), i_end = focusChanges.end(); i != i_end; ++i){
    ArithVar v = (*i).first;
    int focusChange = (*i).second;

    Rational chg(focusChange);
    if(d_tableau.isBasic(v)){
      d_linEq.substitutePlusTimesConstant(inf, v, chg);
    }else{
      d_linEq.directlyAddToCoefficient(inf, v, chg);
    }
  }
}

ArithVar SimplexDecisionProcedure::constructInfeasiblityFunction(TimerStat& timer){
  TimerStat::CodeTimer codeTimer(timer);
  Assert(!d_errorSet.focusEmpty());

  ArithVar inf = requestVariable();
  Assert(inf != ARITHVAR_SENTINEL);

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
  d_tableau.addRow(inf, coeffs, variables);
  DeltaRational newAssignment = d_linEq.computeRowValue(inf, false);
  d_variables.setAssignment(inf, newAssignment);

  d_linEq.trackVariable(inf);

  Debug("Inf") << inf << " " << newAssignment << endl;

  return inf;
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
