/*********************                                                        */
/*! \file sexpr.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simple representation of S-expressions
 **
 ** Simple representation of S-expressions.
 **/

#include <iostream>
#include <vector>

#include "base/cvc4_assert.h"
#include "expr/sexpr.h"
#include "printer/printer.h"



namespace CVC4 {

// std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) {
// # warning "check here"
//   Printer::getPrinter(Expr::setlanguage::getLanguage(out))->toStream(out, sexpr);
//   return out;
// }

std::string SExpr::getValue() const {
  CheckArgument( isAtom(), this );
  switch(d_sexprType) {
  case SEXPR_INTEGER:
    return d_integerValue.toString();
  case SEXPR_RATIONAL: {
    // We choose to represent rationals as decimal strings rather than
    // "numerator/denominator."  Perhaps an additional SEXPR_DECIMAL
    // could be added if we need both styles, even if it's backed by
    // the same Rational object.
    std::stringstream ss;
    ss << std::fixed << d_rationalValue.getDouble();
    return ss.str();
  }
  case SEXPR_STRING:
  case SEXPR_KEYWORD:
    return d_stringValue;
  case SEXPR_NOT_ATOM:
    return std::string();
  }
  return std::string();

}

const CVC4::Integer& SExpr::getIntegerValue() const {
  CheckArgument( isInteger(), this );
  return d_integerValue;
}

const CVC4::Rational& SExpr::getRationalValue() const {
  CheckArgument( isRational(), this );
  return d_rationalValue;
}

const std::vector<SExpr>& SExpr::getChildren() const {
  CheckArgument( !isAtom(), this );
  return d_children;
}

bool SExpr::operator==(const SExpr& s) const {
  return d_sexprType == s.d_sexprType &&
         d_integerValue == s.d_integerValue &&
         d_rationalValue == s.d_rationalValue &&
         d_stringValue == s.d_stringValue &&
         d_children == s.d_children;
}

bool SExpr::operator!=(const SExpr& s) const {
  return !(*this == s);
}


SExpr SExpr::parseAtom(const std::string& atom) {
  if(atom == "true"){
    return SExpr(true);
  } else if(atom == "false"){
    return SExpr(false);
  } else {
    try {
      Integer z(atom);
      return SExpr(z);
    }catch(std::invalid_argument&){
      // Fall through to the next case
    }
    try {
      Rational q(atom);
      return SExpr(q);
    }catch(std::invalid_argument&){
      // Fall through to the next case
    }
    return SExpr(atom);
  }
}

SExpr SExpr::parseListOfAtoms(const std::vector<std::string>& atoms) {
  std::vector<SExpr> parsedAtoms;
  typedef std::vector<std::string>::const_iterator const_iterator;
  for(const_iterator i = atoms.begin(), i_end=atoms.end(); i != i_end; ++i){
    parsedAtoms.push_back(parseAtom(*i));
  }
  return SExpr(parsedAtoms);
}

SExpr SExpr::parseListOfListOfAtoms(const std::vector< std::vector<std::string> >& atoms_lists) {
  std::vector<SExpr> parsedListsOfAtoms;
  typedef std::vector< std::vector<std::string> >::const_iterator const_iterator;
  for(const_iterator i = atoms_lists.begin(), i_end = atoms_lists.end(); i != i_end; ++i){
    parsedListsOfAtoms.push_back(parseListOfAtoms(*i));
  }
  return SExpr(parsedListsOfAtoms);
}
}/* CVC4 namespace */
