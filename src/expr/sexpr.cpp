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
 **
 ** SExprs have their own language specific printing procedures. The reason for
 ** this being implemented on SExpr and not on the Printer class is that the
 ** Printer class lives in libcvc4. It has to currently as it prints fairly
 ** complicated objects, like Model, which in turn uses SmtEngine pointers.
 ** However, SExprs need to be printed by Statistics. To get the output consistent
 ** with the previous version, the printing of SExprs in different languages is
 ** handled in the SExpr class and the libexpr library.
 **/

#include "expr/sexpr.h"

#include <iostream>
#include <sstream>
#include <vector>

#include "base/cvc4_assert.h"
#include "expr/expr.h"
#include "util/smt2_quote_string.h"


namespace CVC4 {

const int PrettySExprs::s_iosIndex = std::ios_base::xalloc();

std::ostream& operator<<(std::ostream& out, PrettySExprs ps) {
  ps.applyPrettySExprs(out);
  return out;
}

#warning "TODO: Discuss this change with Clark."
SExpr::SExpr(bool value) :
    d_sexprType(SEXPR_KEYWORD),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value ? "true" : "false"),
    d_children() {
}

std::string SExpr::toString() const {
  std::stringstream ss;
  ss << (*this);
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) {
  SExpr::toStream(out, sexpr);
  return out;
}

void SExpr::toStream(std::ostream& out, const SExpr& sexpr) throw() {
  toStream(out, sexpr, Expr::setlanguage::getLanguage(out));
}

void SExpr::toStream(std::ostream& out, const SExpr& sexpr, OutputLanguage language) throw() {
  toStream(out, sexpr, language, PrettySExprs::getPrettySExprs(out) ? 2 : 0);
}

void SExpr::toStream(std::ostream& out, const SExpr& sexpr, OutputLanguage language, int indent) throw() {
  if( sexpr.isKeyword() && languageQuotesKeywords(language) ){
    out << quoteSymbol(sexpr.getValue());
  } else {
    toStreamRec(out, sexpr, language, indent);
  }
}


void SExpr::toStreamRec(std::ostream& out, const SExpr& sexpr, OutputLanguage language, int indent) throw() {
  if(sexpr.isInteger()) {
    out << sexpr.getIntegerValue();
  } else if(sexpr.isRational()) {
    out << std::fixed << sexpr.getRationalValue().getDouble();
  } else if(sexpr.isKeyword()) {
    out << sexpr.getValue();
  } else if(sexpr.isString()) {
    std::string s = sexpr.getValue();
    // escape backslash and quote
    for(size_t i = 0; i < s.length(); ++i) {
      if(s[i] == '"') {
        s.replace(i, 1, "\\\"");
        ++i;
      } else if(s[i] == '\\') {
        s.replace(i, 1, "\\\\");
        ++i;
      }
    }
    out << "\"" << s << "\"";
  } else {
    const std::vector<SExpr>& kids = sexpr.getChildren();
    out << (indent > 0 && kids.size() > 1 ? "( " : "(");
    bool first = true;
    for(std::vector<SExpr>::const_iterator i = kids.begin(); i != kids.end(); ++i) {
      if(first) {
        first = false;
      } else {
        if(indent > 0) {
          out << "\n" << std::string(indent, ' ');
        } else {
          out << ' ';
        }
      }
      toStreamRec(out, *i, language, indent <= 0 || indent > 2 ? 0 : indent + 2);
    }
    if(indent > 0 && kids.size() > 1) {
      out << '\n';
      if(indent > 2) {
        out << std::string(indent - 2, ' ');
      }
    }
    out << ')';
  }
}/* toStreamRec() */


bool SExpr::languageQuotesKeywords(OutputLanguage language) {
  switch(language) {
    case language::output::LANG_SMTLIB_V1:
    case language::output::LANG_SMTLIB_V2_0:
    case language::output::LANG_SMTLIB_V2_5:
    case language::output::LANG_SYGUS:
    case language::output::LANG_TPTP:
    case language::output::LANG_Z3STR:
      return true;
    case language::output::LANG_AST:
    case language::output::LANG_CVC3:
    case language::output::LANG_CVC4:
    default:
      return false;
  };
}



std::string SExpr::getValue() const {
  PrettyCheckArgument( isAtom(), this );
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
  PrettyCheckArgument( isInteger(), this );
  return d_integerValue;
}

const CVC4::Rational& SExpr::getRationalValue() const {
  PrettyCheckArgument( isRational(), this );
  return d_rationalValue;
}

const std::vector<SExpr>& SExpr::getChildren() const {
  PrettyCheckArgument( !isAtom(), this );
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
