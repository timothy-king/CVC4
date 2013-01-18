/*********************                                                        */
/*! \file simplex_update.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This implements UpdateInfo.
 **
 ** This implements the UpdateInfo.
 **/


#include "theory/arith/simplex_update.h"
#include "theory/arith/constraint.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {


UpdateInfo::UpdateInfo():
  d_nonbasic(ARITHVAR_SENTINEL),
  d_nonbasicDirection(0),
  d_nonbasicDelta(),
  d_foundConflict(false),
  d_errorsChange(),
  d_focusDirection(),
  d_limiting(NullConstraint),
  d_witness(AntiProductive)
{}

UpdateInfo::UpdateInfo(ArithVar nb, int dir):
  d_nonbasic(nb),
  d_nonbasicDirection(dir),
  d_nonbasicDelta(),
  d_foundConflict(false),
  d_errorsChange(),
  d_focusDirection(),
  d_limiting(NullConstraint),
  d_witness(AntiProductive)
{
  Assert(dir == 1 || dir == -1);
}

UpdateInfo::UpdateInfo(bool conflict, ArithVar nb, const DeltaRational& delta, Constraint c):
  d_nonbasic(nb),
  d_nonbasicDirection(delta.sgn()),
  d_nonbasicDelta(delta),
  d_foundConflict(true),
  d_errorsChange(),
  d_focusDirection(),
  d_limiting(c),
  d_witness(ConflictFound)
{
  Assert(conflict);
}

UpdateInfo UpdateInfo::conflict(ArithVar nb, const DeltaRational& delta, Constraint lim){
  return UpdateInfo(true, nb, delta, lim);
}

void UpdateInfo::updateUnbounded(const DeltaRational& delta, int ec, int f){
  d_limiting = NullConstraint;
  d_nonbasicDelta = delta;
  d_errorsChange = ec;
  d_focusDirection = f;
  updateWitness();
  Assert(unbounded());
  Assert(improvement(d_witness));
  Assert(!describesPivot());
  Assert(debugSgnAgreement());
}
void UpdateInfo::updatePureFocus(const DeltaRational& delta, Constraint c){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange.clear();
  d_focusDirection = 1;
  updateWitness();
  Assert(!describesPivot());
  Assert(improvement(d_witness));
  Assert(debugSgnAgreement());
}

void UpdateInfo::updatePivot(const DeltaRational& delta, Constraint c){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange.clear();
  d_focusDirection.clear();
  updateWitness();
  Assert(describesPivot());
  Assert(debugSgnAgreement());
}

void UpdateInfo::updatePivot(const DeltaRational& delta, Constraint c, int ec){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange = ec;
  d_focusDirection.clear();
  updateWitness();
  Assert(describesPivot());
  Assert(debugSgnAgreement());
}

void UpdateInfo::update(const DeltaRational& delta, Constraint c, int ec, int fd){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange = ec;
  d_focusDirection = fd;
  updateWitness();
  Assert(describesPivot() || improvement(d_witness));
  Assert(debugSgnAgreement());
}

bool UpdateInfo::describesPivot() const {
  return !unbounded() && d_nonbasic != d_limiting->getVariable();
}

void UpdateInfo::output(std::ostream& out) const{
  out << "{UpdateInfo"
      << ", nb = " << d_nonbasic
      << ", dir = " << d_nonbasicDirection
      << ", delta = " << d_nonbasicDelta
      << ", conflict = " << d_foundConflict
      << ", errorChange = " << d_errorsChange
      << ", focusDir = " << d_focusDirection
      << ", limiting = " << d_limiting
      << "}";
}

ArithVar UpdateInfo::leaving() const{
  Assert(describesPivot());

  return d_limiting->getVariable();
}

std::ostream& operator<<(std::ostream& out, const UpdateInfo& up){
  up.output(out);
  return out;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
