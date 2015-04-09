/*********************                                                        */
/*! \file callbacks.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/callbacks.h"
#include "theory/arith/theory_arith_private.h"

namespace CVC4 {
namespace theory {
namespace arith {

SetupLiteralCallBack::SetupLiteralCallBack(TheoryArithPrivate& ta)
  : d_arith(ta)
{}
void SetupLiteralCallBack::operator()(TNode lit){
  TNode atom = (lit.getKind() == kind::NOT) ? lit[0] : lit;
  if(!d_arith.isSetup(atom)){
    d_arith.setupAtom(atom);
  }
}

DeltaComputeCallback::DeltaComputeCallback(const TheoryArithPrivate& ta)
  : d_ta(ta)
{}
Rational DeltaComputeCallback::operator()() const{
  return d_ta.deltaValueForTotalOrder();
}

TempVarMalloc::TempVarMalloc(TheoryArithPrivate& ta)
: d_ta(ta)
{}
ArithVar TempVarMalloc::request(){
  Node skolem = mkRealSkolem("tmpVar");
  return d_ta.requestArithVar(skolem, false, true);
}
void TempVarMalloc::release(ArithVar v){
  d_ta.releaseArithVar(v);
}

BasicVarModelUpdateCallBack::BasicVarModelUpdateCallBack(TheoryArithPrivate& ta)
  : d_ta(ta)
{}
void BasicVarModelUpdateCallBack::operator()(ArithVar x){
  d_ta.signal(x);
}

_RaiseConflict::_RaiseConflict(TheoryArithPrivate& ta)
  : d_ta(ta)
{}

void _RaiseConflict::raiseConflict(ConstraintCP c) const{
  Assert(c->inConflict());
  d_ta.raiseConflict(c);
}

FarkasConflictBuilder::FarkasConflictBuilder()
  : d_farkas()
  , d_constraints()
  , d_firstConstraint(NullConstraint)
{
  reset();
}

bool FarkasConflictBuilder::underConstruction() const{
  return d_firstConstraint != NullConstraint;
}


void FarkasConflictBuilder::reset(){
  d_firstConstraint = NullConstraint;
  d_constraints.clear();
  PROOF(d_farkas.clear());
  PROOF(d_farkas.push_back(Rational(0)));
  Assert(!underConstruction());
}

/* Adds a constraint to the constraint under construction. */
void FarkasConflictBuilder::addConstraint(ConstraintCP c, const Rational& fc){
  Assert(!PROOF_ON() || d_constraints.size() + 1 == d_farkas.size());
  Assert(PROOF_ON() || d_farkas.empty());
  Assert(c->isTrue());
  
  if(d_firstConstraint == NullConstraint){
    d_firstConstraint = c;
  } else {
    d_constraints.push_back(c);
  }
  PROOF(d_farkas.push_back(fc));
}

/* Turns the vector under construction into a conflict */
ConstraintCP FarkasConflictBuilder::commitConflict(){
  Assert(underConstruction());
  Assert(!d_constraints.empty());
  Assert(!PROOF_ON() || d_constraints.size() + 1 == d_farkas.size());
  Assert(PROOF_ON() || d_farkas.empty());

  ConstraintP not_c = d_firstConstraint->getNegation();
  RationalVectorCP coeffs = NULLPROOF(&d_farkas);
  not_c->impliedByFarkas(d_constraints, coeffs, true );

  reset();
  Assert(!underConstruction());
  Assert( not_c->inConflict() );
  return not_c;
}

RaiseEqualityEngineConflict::RaiseEqualityEngineConflict(TheoryArithPrivate& ta)
  : d_ta(ta)
{}

/* If you are not an equality engine, don't use this! */
void RaiseEqualityEngineConflict::raiseEEConflict(Node n) const{
  d_ta.raiseBlackBoxConflict(n);
}


BoundCountingLookup::BoundCountingLookup(TheoryArithPrivate& ta)
: d_ta(ta)
{}

const BoundsInfo& BoundCountingLookup::boundsInfo(ArithVar basic) const{
  return d_ta.boundsInfo(basic);
}

BoundCounts BoundCountingLookup::atBounds(ArithVar basic) const{
  return boundsInfo(basic).atBounds();
}
BoundCounts BoundCountingLookup::hasBounds(ArithVar basic) const {
  return boundsInfo(basic).hasBounds();
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
