/*********************                                                        */
/*! \file rational_cln_imp.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Morgan Deters, Christopher L. Conway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multi-precision rational constant.
 **
 ** A multi-precision rational constant.
 **/

#include "cvc4autoconfig.h"
#include "util/rational.h"
#include <string>
#include <sstream>

#ifndef CVC4_CLN_IMP
#  error "This source should only ever be built if CVC4_CLN_IMP is on !"
#endif /* CVC4_CLN_IMP */

using namespace std;
using namespace CVC4;

/* Computes a rational given a decimal string. The rational
 * version of <code>xxx.yyy</code> is <code>xxxyyy/(10^3)</code>.
 */
Rational Rational::fromDecimal(const std::string& dec) {
  // Find the decimal point, if there is one
  string::size_type i( dec.find(".") );
  if( i != string::npos ) {
    /* Erase the decimal point, so we have just the numerator. */
    Integer numerator( string(dec).erase(i,1) );

    /* Compute the denominator: 10 raise to the number of decimal places */
    int decPlaces = dec.size() - (i + 1);
    Integer denominator( Integer(10).pow(decPlaces) );

    return Rational( numerator, denominator );
  } else {
    /* No decimal point, assume it's just an integer. */
    return Rational( dec );
  }
}

std::ostream& CVC4::operator<<(std::ostream& os, const Rational& q){
  return os << q.toString();
}



/** Equivalent to calling (this->abs()).cmp(b.abs()) */
int Rational::absCmp(const Rational& q) const{
  const Rational& r = *this;
  int rsgn = r.sgn();
  int qsgn = q.sgn();
  if(rsgn == 0){
    return (qsgn == 0) ? 0 : -1;
  }else if(qsgn == 0){
    Assert(rsgn != 0);
    return 1;
  }else if((rsgn > 0) && (qsgn > 0)){
    return r.cmp(q);
  }else if((rsgn < 0) && (qsgn < 0)){
    // if r < q < 0, q.cmp(r) = +1, (r.abs()).cmp(q.abs()) = +1
    // if q < r < 0, q.cmp(r) = -1, (r.abs()).cmp(q.abs()) = -1
    // if q = r < 0, q.cmp(r) =  0, (r.abs()).cmp(q.abs()) =  0
    return q.cmp(r);
  }else if((rsgn < 0) && (qsgn > 0)){
    Rational rpos = -r;
    return rpos.cmp(q);
  }else {
    Assert(rsgn > 0 && (qsgn < 0));
    Rational qpos = -q;
    return r.cmp(qpos);
  }
}

Rational Rational::fromDouble(double d) throw(RationalFromDoubleException){
  try{
    cln::cl_DF fromD = d;
    Rational q;
    q.d_value = cln::rationalize(fromD);
    return q;
  }catch(cln::floating_point_underflow_exception& fpue){
    throw RationalFromDoubleException(d);
  }catch(cln::floating_point_nan_exception& fpne){
    throw RationalFromDoubleException(d);
  }catch(cln::floating_point_overflow_exception& fpoe){
    throw RationalFromDoubleException(d);
  }
}

RationalFromDoubleException::RationalFromDoubleException(double d) throw()
  : Exception()
{
  std::stringstream ss;
  ss << "RationalFromDoubleException(";
  ss << d;
  ss << ")";
  setMessage(ss.str());
}

/** Integer power function.*/
Rational Rational::pow(unsigned long p) const{
  CheckArgument(p >= 0, this, "Negative integer passed to Rational::pow()");
  if(p == 0){
    return Rational(1);
  } else {
    cln::cl_I exp(p);
    cln::cl_RA pow = cln::expt_pos(d_value, exp);
    return Rational(pow);
  }
}
