/*********************                                                        */
/*! \file partial_model.cpp
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


#include "theory/arith/partial_model.h"
#include "util/output.h"
#include "theory/arith/constraint.h"
#include "theory/arith/normal_form.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

ArithVariables::ArithVariables(context::Context* c, RationalCallBack& deltaComputingFunc)
 : d_vars(),
   d_safeAssignment(),
   d_numberOfVariables(0),
   d_pool(),
   d_released(),
   d_nodeToArithVarMap(),
   d_lbRevertHistory(c, true, LowerBoundCleanUp(this)),
   d_ubRevertHistory(c, true, UpperBoundCleanUp(this)),
   d_deltaIsSafe(false),
   d_delta(-1,1),
   d_deltaComputingFunc(deltaComputingFunc)
{ }

ArithVariables::VarInfo::VarInfo()
  : d_var(ARITHVAR_SENTINEL),
    d_assignment(0),
    d_lb(NullConstraint),
    d_ub(NullConstraint),
    d_cmpAssignmentLB(1),
    d_cmpAssignmentUB(-1),
    d_pushCount(0),
    d_node(Node::null()),
    d_slack(false)
{ }

void ArithVariables::VarInfo::initialize(ArithVar v, Node n, bool slack){
  Assert(!initialized());
  Assert(d_lb == NullConstraint);
  Assert(d_ub == NullConstraint);
  Assert(d_cmpAssignmentLB > 0);
  Assert(d_cmpAssignmentUB < 0);
  d_var = v;
  d_node = n;
  d_slack = slack;

  if(d_slack){
    //The type computation is not quite accurate for Rationals that are 
    //integral.
    //We'll use the isIntegral check from the polynomial package instead.
    Polynomial p = Polynomial::parsePolynomial(n);
    d_type = p.isIntegral() ? ATInteger : ATReal;
  }else{
    d_type = nodeToArithType(n);
  }

  Assert(initialized());
}
void ArithVariables::VarInfo::uninitialize(){
  d_var = ARITHVAR_SENTINEL;
  d_node = Node::null();
}

void ArithVariables::VarInfo::setAssignment(const DeltaRational& a){
  Assert(initialized());
  d_assignment = a;
  if(d_ub != NullConstraint){
    d_cmpAssignmentUB = d_assignment.cmp(d_ub->getValue());
  }
  if(d_lb != NullConstraint){
    d_cmpAssignmentLB = d_assignment.cmp(d_lb->getValue());
  }
}

void ArithVariables::releaseArithVar(ArithVar v){
  VarInfo& vi = d_vars.get(v);
  vi.uninitialize();
  if(vi.canBeReclaimed()){
    d_pool.push_back(v);
  }else{
    d_released.push_back(v);
  }
}

void ArithVariables::VarInfo::setUpperBound(Constraint ub){
  Assert(initialized());
  d_ub = ub;
  if(d_ub == NullConstraint){
    d_cmpAssignmentUB = -1;
  }else{
    d_cmpAssignmentUB = d_assignment.cmp(d_ub->getValue());
  }
}

void ArithVariables::VarInfo::setLowerBound(Constraint lb){
  Assert(initialized());
  d_lb = lb;
  if(d_lb == NullConstraint){
    d_cmpAssignmentLB = 1;
  }else{
    d_cmpAssignmentLB = d_assignment.cmp(d_lb->getValue());
  }
}

void ArithVariables::attemptToReclaimReleased(){
  std::list<ArithVar>::iterator i = d_released.begin();
  std::list<ArithVar>::iterator i_end = d_released.end(); 
  for(int iter = 0; iter < 20 && i != i_end; ++iter){
    ArithVar v = *i;
    VarInfo& vi = d_vars.get(v);
    if(vi.canBeReclaimed()){
      d_pool.push_back(v);
      std::list<ArithVar>::iterator curr = i;
      ++i;
      d_released.erase(curr);
    }else{
      ++i;
    }
  }
}

ArithVar ArithVariables::allocateVariable(){
  if(d_pool.empty()){
    attemptToReclaimReleased();
  }
  bool reclaim = !d_pool.empty();
  
  ArithVar varX;
  if(reclaim){
    varX = d_pool.back();
    d_pool.pop_back();
  }else{
    varX = d_numberOfVariables;
    ++d_numberOfVariables;
  }
  d_vars.set(varX, VarInfo());
  return varX;
}


const Rational& ArithVariables::getDelta(){
  if(!d_deltaIsSafe){
    Rational nextDelta = d_deltaComputingFunc();
    setDelta(nextDelta);
  }
  Assert(d_deltaIsSafe);
  return d_delta;
}

bool ArithVariables::boundsAreEqual(ArithVar x) const{
  if(hasLowerBound(x) && hasUpperBound(x)){
    return getUpperBound(x) == getLowerBound(x);
  }else{
    return false;
  }
}

void ArithVariables::setAssignment(ArithVar x, const DeltaRational& r){
  Debug("partial_model") << "pm: updating the assignment to" << x
                         << " now " << r <<endl;
  VarInfo& vi = d_vars.get(x);
  if(!d_safeAssignment.isKey(x)){
    d_safeAssignment.set(x, vi.d_assignment);
  }
  invalidateDelta();
  vi.setAssignment(r);
}

void ArithVariables::setAssignment(ArithVar x, const DeltaRational& safe, const DeltaRational& r){
  Debug("partial_model") << "pm: updating the assignment to" << x
                         << " now " << r <<endl;
  if(safe == r){
    if(d_safeAssignment.isKey(x)){
      d_safeAssignment.remove(x);
    }
  }else{
    d_safeAssignment.set(x, safe);
  }

  invalidateDelta();
  VarInfo& vi = d_vars.get(x);
  vi.setAssignment(r);
}

void ArithVariables::initialize(ArithVar x, Node n, bool slack){
  VarInfo& vi = d_vars.get(x);
  vi.initialize(x, n, slack);
  d_nodeToArithVarMap[n] = x;
}

ArithVar ArithVariables::allocate(Node n, bool slack){
  ArithVar v = allocateVariable();
  initialize(v, n, slack);
  return v;
}

// void ArithVariables::initialize(ArithVar x, const DeltaRational& r){
//   Assert(x == d_mapSize);
//   Assert(equalSizes());
//   ++d_mapSize;

//   // Is worth mentioning that this is not strictly necessary, but this maintains the internal invariant
//   // that when d_assignment is set this gets set.
//   invalidateDelta();
//   d_assignment.push_back( r );

//   d_boundRel.push_back(BetweenBounds);

//   d_ubc.push_back(NullConstraint);
//   d_lbc.push_back(NullConstraint);
// }

/** Must know that the bound exists both calling this! */
const DeltaRational& ArithVariables::getUpperBound(ArithVar x) const {
  Assert(inMaps(x));
  Assert(hasUpperBound(x));

  return getUpperBoundConstraint(x)->getValue();
}

const DeltaRational& ArithVariables::getLowerBound(ArithVar x) const {
  Assert(inMaps(x));
  Assert(hasLowerBound(x));

  return getLowerBoundConstraint(x)->getValue();
}

const DeltaRational& ArithVariables::getSafeAssignment(ArithVar x) const{
  Assert(inMaps(x));
  if(d_safeAssignment.isKey(x)){
    return d_safeAssignment[x];
  }else{
    return d_vars[x].d_assignment;
  }
}

const DeltaRational& ArithVariables::getAssignment(ArithVar x, bool safe) const{
  Assert(inMaps(x));
  if(safe && d_safeAssignment.isKey(x)){
    return d_safeAssignment[x];
  }else{
    return d_vars[x].d_assignment;
  }
}

const DeltaRational& ArithVariables::getAssignment(ArithVar x) const{
  Assert(inMaps(x));
  return d_vars[x].d_assignment;
}


void ArithVariables::setLowerBoundConstraint(Constraint c){
  AssertArgument(c != NullConstraint, "Cannot set a lower bound to NullConstraint.");
  AssertArgument(c->isEquality() || c->isLowerBound(),
                 "Constraint type must be set to an equality or UpperBound.");
  ArithVar x = c->getVariable();
  Debug("partial_model") << "setLowerBoundConstraint(" << x << ":" << c << ")" << endl;
  Assert(inMaps(x));
  Assert(greaterThanLowerBound(x, c->getValue()));

  invalidateDelta();
  VarInfo& vi = d_vars.get(x);
  pushLowerBound(vi);
  vi.setLowerBound(c);
}

void ArithVariables::setUpperBoundConstraint(Constraint c){
  AssertArgument(c != NullConstraint, "Cannot set a upper bound to NullConstraint.");
  AssertArgument(c->isEquality() || c->isUpperBound(),
                 "Constraint type must be set to an equality or UpperBound.");

  ArithVar x = c->getVariable();
  Debug("partial_model") << "setUpperBoundConstraint(" << x << ":" << c << ")" << endl;
  Assert(inMaps(x));
  Assert(lessThanUpperBound(x, c->getValue()));

  invalidateDelta();
  VarInfo& vi = d_vars.get(x);
  pushUpperBound(vi);
  vi.setUpperBound(c);
}

void ArithVariables::forceRelaxLowerBound(ArithVar v){
  AssertArgument(inMaps(v), "Calling forceRelaxLowerBound on a variable that is not properly setup.");
  AssertArgument(hasLowerBound(v), "Calling forceRelaxLowerBound on a variable without a lowerbound.");

  Debug("partial_model") << "forceRelaxLowerBound(" << v << ") dropping :" << getLowerBoundConstraint(v) << endl;

  invalidateDelta();
  VarInfo& vi = d_vars.get(v);
  pushLowerBound(vi);
  vi.setLowerBound(NullConstraint);
}


void ArithVariables::forceRelaxUpperBound(ArithVar v){
  AssertArgument(inMaps(v), "Calling forceRelaxUpperBound on a variable that is not properly setup.");
  AssertArgument(hasUpperBound(v), "Calling forceRelaxUpperBound on a variable without an upper bound.");

  Debug("partial_model") << "forceRelaxUpperBound(" << v << ") dropping :" << getUpperBoundConstraint(v) << endl;

  invalidateDelta();
  VarInfo& vi = d_vars.get(v);
  pushUpperBound(vi);
  vi.setUpperBound(NullConstraint);
}

int ArithVariables::cmpToLowerBound(ArithVar x, const DeltaRational& c) const{
  if(!hasLowerBound(x)){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return 1;
  }else{
    return c.cmp(getLowerBound(x));
  }
}

int ArithVariables::cmpToUpperBound(ArithVar x, const DeltaRational& c) const{
  if(!hasUpperBound(x)){
    //u = \intfy
    // ? c > \infty |-  _|_
    return -1;
  }else{
    return c.cmp(getUpperBound(x));
  }
}

bool ArithVariables::equalsLowerBound(ArithVar x, const DeltaRational& c){
  if(!hasLowerBound(x)){
    return false;
  }else{
    return c == getLowerBound(x);
  }
}
bool ArithVariables::equalsUpperBound(ArithVar x, const DeltaRational& c){
  if(!hasUpperBound(x)){
    return false;
  }else{
    return c == getUpperBound(x);
  }
}

bool ArithVariables::hasEitherBound(ArithVar x) const{
  return hasLowerBound(x) || hasUpperBound(x);
}

bool ArithVariables::strictlyBelowUpperBound(ArithVar x) const{
  return d_vars[x].d_cmpAssignmentUB < 0;
  // if(!hasUpperBound(x)){ // u = \infty
  //   return true;
  // }else{
  //   return d_assignment[x] < getUpperBound(x);
  // }
}

bool ArithVariables::strictlyAboveLowerBound(ArithVar x) const{
  return d_vars[x].d_cmpAssignmentLB > 0;
  // if(!hasLowerBound(x)){ // l = -\infty
  //   return true;
  // }else{
  //   return getLowerBound(x) < d_assignment[x];
  // }
}

bool ArithVariables::assignmentIsConsistent(ArithVar x) const{
  return
    d_vars[x].d_cmpAssignmentLB >= 0 &&
    d_vars[x].d_cmpAssignmentUB <= 0;
  // const DeltaRational& beta = getAssignment(x);

  // //l_i <= beta(x_i) <= u_i
  // return  greaterThanLowerBound(x,beta) && lessThanUpperBound(x,beta);
}


void ArithVariables::clearSafeAssignments(bool revert){

  if(revert && !d_safeAssignment.empty()){
    invalidateDelta();
  }

  while(!d_safeAssignment.empty()){
    ArithVar atBack = d_safeAssignment.back();
    if(revert){
      VarInfo& vi = d_vars.get(atBack);
      vi.setAssignment(d_safeAssignment[atBack]);
    }
    d_safeAssignment.pop_back();
  }
}

void ArithVariables::revertAssignmentChanges(){
  clearSafeAssignments(true);
}
void ArithVariables::commitAssignmentChanges(){
  clearSafeAssignments(false);
}

void ArithVariables::printModel(ArithVar x){
  Debug("model") << "model" << x << ":"<< getAssignment(x) << " ";
  if(!hasLowerBound(x)){
    Debug("model") << "no lb ";
  }else{
    Debug("model") << getLowerBound(x) << " ";
    Debug("model") << getLowerBoundConstraint(x) << " ";
  }
  if(!hasUpperBound(x)){
    Debug("model") << "no ub ";
  }else{
    Debug("model") << getUpperBound(x) << " ";
    Debug("model") << getUpperBoundConstraint(x) << " ";
  }
  Debug("model") << endl;
}


// BoundRelationship ArithVariables::boundRelationship(Constraint lb, const DeltaRational& d, Constraint ub){
//   if(lb == NullConstraint && ub == NullConstraint){
//     return BetweenBounds;
//   }else if(lb == NullConstraint){
//     int cmp = d.cmp(ub->getValue());
//     return (cmp < 0) ? BetweenBounds :
//       (cmp == 0 ? AtUpperBound  : AboveUpperBound);
//   }else if(ub == NullConstraint){
//     int cmp = d.cmp(lb->getValue());
//     return (cmp > 0) ? BetweenBounds :
//       (cmp == 0 ? AtLowerBound  : BelowLowerBound);    
//   }else{
//     Assert(lb->getValue() <= ub->getValue());
//     int cmpToLB = d.cmp(lb->getValue());
//     if(cmpToLB < 0){
//       return BelowLowerBound;
//     }else if(cmpToLB == 0){
//       return (d == ub->getValue()) ? AtBothBounds : AtLowerBound;
//     }else{
//       // d > 0
//       int cmpToUB = d.cmp(ub->getValue());
//       return (cmpToUB > 0) ? BetweenBounds :
//         (cmpToUB == 0 ? AtLowerBound  : BelowLowerBound);    
//     }
//   }
// }

void ArithVariables::pushUpperBound(VarInfo& vi){
  ++vi.d_pushCount;
  d_ubRevertHistory.push_back(make_pair(vi.d_var, vi.d_ub));
}
void ArithVariables::pushLowerBound(VarInfo& vi){
  ++vi.d_pushCount;
  d_lbRevertHistory.push_back(make_pair(vi.d_var, vi.d_lb));
}

void ArithVariables::popUpperBound(AVCPair* c){
  VarInfo& vi = d_vars.get((*c).first);
  vi.setUpperBound((*c).second);
  --vi.d_pushCount;
}

void ArithVariables::popLowerBound(AVCPair* c){
  VarInfo& vi = d_vars.get((*c).first);
  vi.setLowerBound((*c).second);
  --vi.d_pushCount;
}

/* To ensure that the final deallocation stuff works,
 * we need to ensure that we need to not reference any of the other vectors
 */
// void ArithVariables::relaxUpperBound(Constraint curr, Constraint afterPop){
//   BoundRelation next = Undefined;
//   switch(d_boundRel[x]){
//   case BelowLowerBound:
//   case BetweenBounds:
//   case AtLowerBound:
//     return; // do nothing
//   case AtUpperBound:
//     if(afterPop != NullConstraint
//        && curr->getValue() == afterPop->getValue()){
//       next = AtUpperBound;
//     }else{
//       next = BetweenBounds;
//     }
//     break;
//   case AtBothBounds:
//     if(afterPop != NullConstraint
//        && curr->getValue() == afterPop->getValue()){
//       next = AtUpperBound;
//     }else{
//       next = AtLowerBound;
//     }
//     break;
//   case AboveUpperBound:
//     if(afterPop == NullConstraint){
//       next = BetweenBounds;
//     }else{
//       int cmp = d_assignment[x].cmp(afterPop->getValue());
//       next = (cmp < 0) ? BetweenBounds :
//         (cmp == 0) ? AtUpperBound  : AboveUpperBound;
//     }
//     break;
//   default:
//     Unreachable();
//   }
//   d_boundRel[x] = next;
// }



// void ArithVariables::relaxLowerBound(Constraint curr, Constraint afterPop){
//   // TODO this can be optimized using the automata induced by d_boundRel and
//   // the knowledge that lb <= ub
//   ArithVar x = curr->getVariable();
//   d_boundRel[x] = boundRelationship(afterPop, d_assignment[x], d_ubc[x]);    
// }

void ArithVariables::LowerBoundCleanUp::operator()(AVCPair* p){
  d_pm->popLowerBound(p);
}

void ArithVariables::UpperBoundCleanUp::operator()(AVCPair* p){
  d_pm->popUpperBound(p);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
