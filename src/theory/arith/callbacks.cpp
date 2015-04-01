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

void _RaiseConflict::raiseConflict(ConstraintCP c){
  Assert(c->inConflict());
  d_ta.raiseConflict(c);
}

FarkasConflictBuilder::FarkasConflictBuilder(_RaiseConflict& rc)
  : d_raiseConflict(d_raiseConflict)
  , d_finalCoeffSet(false)
  , d_farkas()
  , d_constraints()
{
  reset();
}

bool RaiseFarkasConflict::underConstruction() const{
  return !d_constraints.empty() || d_finalCoeffSet;
}


RaiseFarkasConflict::reset(){
  d_constraints.clear();
  d_finalCoeffSet = false;
  PROOF(d_farkas.clear());
  PROOF(d_farkas.push_back(Rational(0)));
  Assert(!underConstruction());
}

/* Adds a constraint to the constraint under construction. */
void RaiseFarkasConflict::addConstraint(ConstraintCP c, const Rational& fc){
  Assert(!PROOF_ON() || d_constraints.size() + 1 == d_farkas.size());
  Assert(PROOF_ON() || d_farkas.empty());
  
  d_constraints.push_back(c);
  PROOF(d_farkas.push_back(fc));
}


void FarkasConflictBuilder::setFinalCoefficient( const Rational& fc ){
  Assert(!d_finalCoeffSet);
  d_finalCoeffSet = true;
  PROOF(d_farkas.front() == fc);
}

void RaiseFarkasConflict::commitConflict(ConstraintCP c, const Rational& fc){
  setFinalCoefficient(fc);
  commitConflict(c);
}

/* Turns the vector under construction into a conflict */
void RaiseFarkasConflict::commitConflict(ConstraintCP c){
  Assert(underConstruction());
  Assert(!d_constraints.empty());
  Assert(d_finalCoeffSet);
  Assert(!PROOF_ON() || d_constraints.size() + 1 == d_farkas.size());
  Assert(PROOF_ON() || d_farkas.empty());
  Assert(c->hasProof());

  ConstraintP not_c = c->getNegation();
  RationalVectorCP coeffs = NULLPROOF(&d_farkas);
  not_c->_impliedByFarkas(&d_constraints, coeffs );
  d_ta.raiseConflict(not_c);

  reset();
  Assert(!underConstruction());
}

RaiseEqualityEngineConflict::RaiseEqualityEngineConflict(TheoryArithPrivate& ta)
  : d_ta(ta)
{}

/* If you are not an equality engine, don't use this! */
void RaiseEqualityEngineConflict::blackBoxConflict(Node n){
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
