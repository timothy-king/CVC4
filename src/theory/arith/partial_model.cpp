/*********************                                                        */
/*! \file partial_model.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

ArithVariables::ArithVariables(context::Context* c, DeltaComputeCallback deltaComputingFunc)
 : d_vars(),
   d_safeAssignment(),
   d_numberOfVariables(0),
   d_pool(),
   d_released(),
   d_releasedIterator(d_released.begin()),
   d_nodeToArithVarMap(),
   d_boundsQueue(),
   d_enqueueingBoundCounts(true),
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

bool ArithVariables::VarInfo::initialized() const {
  return d_var != ARITHVAR_SENTINEL;
}

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

bool ArithVariables::VarInfo::setAssignment(const DeltaRational& a, BoundsInfo& prev){
  Assert(initialized());
  d_assignment = a;
  int cmpUB = (d_ub == NullConstraint) ? -1 :
    d_assignment.cmp(d_ub->getValue());

  int cmpLB = (d_lb == NullConstraint) ? 1 :
    d_assignment.cmp(d_lb->getValue());

  bool lbChanged = cmpLB != d_cmpAssignmentLB &&
    (cmpLB == 0 || d_cmpAssignmentLB == 0);
  bool ubChanged = cmpUB != d_cmpAssignmentUB &&
    (cmpUB == 0 || d_cmpAssignmentUB == 0);

  if(lbChanged || ubChanged){
    prev = boundsInfo();
  }

  d_cmpAssignmentUB = cmpUB;
  d_cmpAssignmentLB = cmpLB;
  return lbChanged || ubChanged;
}

void ArithVariables::releaseArithVar(ArithVar v){
  VarInfo& vi = d_vars.get(v);
  vi.uninitialize();

  if(d_safeAssignment.isKey(v)){
    d_safeAssignment.remove(v);
  }
  if(vi.canBeReclaimed()){
    d_pool.push_back(v);
  }else{
    d_released.push_back(v);
  }
}

bool ArithVariables::VarInfo::setUpperBound(Constraint ub, BoundsInfo& prev){
  Assert(initialized());
  bool wasNull = d_ub == NullConstraint;
  bool isNull = ub == NullConstraint;

  int cmpUB = isNull ? -1 : d_assignment.cmp(ub->getValue());
  bool ubChanged = (wasNull != isNull) ||
    (cmpUB != d_cmpAssignmentUB && (cmpUB == 0 || d_cmpAssignmentUB == 0));
  if(ubChanged){
    prev = boundsInfo();
  }
  d_ub = ub;
  d_cmpAssignmentUB = cmpUB;
  return ubChanged;
}

bool ArithVariables::VarInfo::setLowerBound(Constraint lb, BoundsInfo& prev){
  Assert(initialized());
  bool wasNull = d_lb == NullConstraint;
  bool isNull = lb == NullConstraint;

  int cmpLB = isNull ? 1 : d_assignment.cmp(lb->getValue());

  bool lbChanged = (wasNull != isNull) ||
    (cmpLB != d_cmpAssignmentLB && (cmpLB == 0 || d_cmpAssignmentLB == 0));
  if(lbChanged){
    prev = boundsInfo();
  }
  d_lb = lb;
  d_cmpAssignmentLB = cmpLB;
  return lbChanged;
}

BoundCounts ArithVariables::VarInfo::atBoundCounts() const {
  uint32_t lbIndc = (d_cmpAssignmentLB == 0) ? 1 : 0;
  uint32_t ubIndc = (d_cmpAssignmentUB == 0) ? 1 : 0;
  return BoundCounts(lbIndc, ubIndc);
}

BoundCounts ArithVariables::VarInfo::hasBoundCounts() const {
  uint32_t lbIndc = (d_lb != NullConstraint) ? 1 : 0;
  uint32_t ubIndc = (d_ub != NullConstraint) ? 1 : 0;
  return BoundCounts(lbIndc, ubIndc);
}

BoundsInfo ArithVariables::VarInfo::boundsInfo() const{
  return BoundsInfo(atBoundCounts(), hasBoundCounts());
}

bool ArithVariables::VarInfo::canBeReclaimed() const{
  return d_pushCount == 0;
}

void ArithVariables::attemptToReclaimReleased(){
  std::list<ArithVar>::iterator i_end = d_released.end();
  for(int iter = 0; iter < 20 && d_releasedIterator != i_end; ++d_releasedIterator){
    ArithVar v = *d_releasedIterator;
    VarInfo& vi = d_vars.get(v);
    if(vi.canBeReclaimed()){
      d_pool.push_back(v);
      std::list<ArithVar>::iterator curr = d_releasedIterator;
      ++d_releasedIterator;
      d_released.erase(curr);
    }else{
      ++d_releasedIterator;
    }
  }
  if(d_releasedIterator == i_end){
    d_releasedIterator = d_released.begin();
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


std::pair<Constraint, Constraint> ArithVariables::explainEqualBounds(ArithVar x) const{
  Assert(boundsAreEqual(x));

  Constraint lb = getLowerBoundConstraint(x);
  Constraint ub = getUpperBoundConstraint(x);
  if(lb->isEquality()){
    return make_pair(lb, NullConstraint);
  }else if(ub->isEquality()){
    return make_pair(ub, NullConstraint);
  }else{
    return make_pair(lb, ub);
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

  BoundsInfo prev;
  if(vi.setAssignment(r, prev)){
    addToBoundQueue(x, prev);
  }
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
  BoundsInfo prev;
  if(vi.setAssignment(r, prev)){
    addToBoundQueue(x, prev);
  }
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
  BoundsInfo prev;
  if(vi.setLowerBound(c, prev)){
    addToBoundQueue(x, prev);
  }
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
  BoundsInfo prev;
  if(vi.setUpperBound(c, prev)){
    addToBoundQueue(x, prev);
  }
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
}

bool ArithVariables::strictlyAboveLowerBound(ArithVar x) const{
  return d_vars[x].d_cmpAssignmentLB > 0;
}

bool ArithVariables::assignmentIsConsistent(ArithVar x) const{
  return
    d_vars[x].d_cmpAssignmentLB >= 0 &&
    d_vars[x].d_cmpAssignmentUB <= 0;
}


void ArithVariables::clearSafeAssignments(bool revert){

  if(revert && !d_safeAssignment.empty()){
    invalidateDelta();
  }

  while(!d_safeAssignment.empty()){
    ArithVar atBack = d_safeAssignment.back();
    if(revert){
      VarInfo& vi = d_vars.get(atBack);
      BoundsInfo prev;
      if(vi.setAssignment(d_safeAssignment[atBack], prev)){
        addToBoundQueue(atBack, prev);
      }
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

void ArithVariables::printEntireModel(std::ostream& out) const{
  out << "---Printing Model ---" << std::endl;
  for(var_iterator i = var_begin(), iend = var_end(); i != iend; ++i){
    printModel(*i, out);
  }
  out << "---Done Model ---" << std::endl;
}

void ArithVariables::printModel(ArithVar x, std::ostream& out) const{
  out << "model" << x << ": "
      << asNode(x) << " "
      << getAssignment(x) << " ";
  if(!hasLowerBound(x)){
    out << "no lb ";
  }else{
    out << getLowerBound(x) << " ";
    out << getLowerBoundConstraint(x) << " ";
  }
  if(!hasUpperBound(x)){
    out << "no ub ";
  }else{
    out << getUpperBound(x) << " ";
    out << getUpperBoundConstraint(x) << " ";
  }
  out << endl;
}

void ArithVariables::printModel(ArithVar x) const{
  printModel(x,  Debug("model"));
}

void ArithVariables::pushUpperBound(VarInfo& vi){
  ++vi.d_pushCount;
  d_ubRevertHistory.push_back(make_pair(vi.d_var, vi.d_ub));
}
void ArithVariables::pushLowerBound(VarInfo& vi){
  ++vi.d_pushCount;
  d_lbRevertHistory.push_back(make_pair(vi.d_var, vi.d_lb));
}

void ArithVariables::popUpperBound(AVCPair* c){
  ArithVar x = c->first;
  VarInfo& vi = d_vars.get(x);
  BoundsInfo prev;
  if(vi.setUpperBound(c->second, prev)){
    addToBoundQueue(x, prev);
  }
  --vi.d_pushCount;
}

void ArithVariables::popLowerBound(AVCPair* c){
  ArithVar x = c->first;
  VarInfo& vi = d_vars.get(x);
  BoundsInfo prev;
  if(vi.setLowerBound(c->second, prev)){
    addToBoundQueue(x, prev);
  }
  --vi.d_pushCount;
}

void ArithVariables::addToBoundQueue(ArithVar v, const BoundsInfo& prev){
  if(d_enqueueingBoundCounts && !d_boundsQueue.isKey(v)){
    d_boundsQueue.set(v, prev);
  }
}

BoundsInfo ArithVariables::selectBoundsInfo(ArithVar v, bool old) const {
  if(old && d_boundsQueue.isKey(v)){
    return d_boundsQueue[v];
  }else{
    return boundsInfo(v);
  }
}

bool ArithVariables::boundsQueueEmpty() const {
  return d_boundsQueue.empty();
}

void ArithVariables::processBoundsQueue(BoundUpdateCallback& changed){
  while(!boundsQueueEmpty()){
    ArithVar v = d_boundsQueue.back();
    BoundsInfo prev = d_boundsQueue[v];
    d_boundsQueue.pop_back();
    BoundsInfo curr = boundsInfo(v);
    if(prev != curr){
      changed(v, prev);
    }
  }
}

void ArithVariables::LowerBoundCleanUp::operator()(AVCPair* p){
  d_pm->popLowerBound(p);
}

void ArithVariables::UpperBoundCleanUp::operator()(AVCPair* p){
  d_pm->popUpperBound(p);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
