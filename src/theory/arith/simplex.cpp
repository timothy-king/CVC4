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
  , d_focusSgns()
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
      d_linEq.trackVariable(curr);

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

  Debug("pu") << d_focusErrorVar << " " << newAssignment << endl;
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
}


void SimplexDecisionProcedure::loadFocusSigns(){
  Assert(d_focusSgns.empty());
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(d_focusErrorVar); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    d_focusSgns.set(curr, e.getCoefficient().sgn());
  }
}

void SimplexDecisionProcedure::unloadFocusSigns(){
  d_focusSgns.purge();
}

int SimplexDecisionProcedure::focusSgn(ArithVar nb) const {
  if(d_focusSgns.isKey(nb)){
    return d_focusSgns[nb];
  }else{
    return 0;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
