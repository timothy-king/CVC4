/*********************                                                        */
/*! \file sexpr.h
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: Tim King, Morgan Deters
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simple representation of S-expressions
 **
 ** Simple representation of S-expressions.
 ** These are used when a simple, and obvious interface for basic
 ** expressions is appropraite.
 **
 ** These are quite ineffecient.
 ** These are totally disconnected from any ExprManager.
 ** These keep unique copies of all of their children.
 ** These are VERY overly verbose and keep much more data than is needed.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SEXPR_H
#define __CVC4__SEXPR_H

#include <iomanip>
#include <sstream>
#include <string>
#include <vector>

#include "base/integer.h"
#include "base/rational.h"
#include "base/exception.h"

namespace CVC4 {

class CVC4_PUBLIC SExprKeyword {
  std::string d_str;
public:
  SExprKeyword(const std::string& s) : d_str(s) {}
  const std::string& getString() const { return d_str; }
};/* class SExpr::Keyword */

/**
 * A simple S-expression. An S-expression is either an atom with a
 * string value, or a list of other S-expressions.
 */
class CVC4_PUBLIC SExpr {

  enum SExprTypes {
    SEXPR_STRING,
    SEXPR_KEYWORD,
    SEXPR_INTEGER,
    SEXPR_RATIONAL,
    SEXPR_NOT_ATOM
  } d_sexprType;

  /** The value of an atomic integer-valued S-expression. */
  CVC4::Integer d_integerValue;

  /** The value of an atomic rational-valued S-expression. */
  CVC4::Rational d_rationalValue;

  /** The value of an atomic S-expression. */
  std::string d_stringValue;

  /** The children of a list S-expression. */
  std::vector<SExpr> d_children;

public:

  typedef SExprKeyword Keyword;

  SExpr() :
    d_sexprType(SEXPR_STRING),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  explicit SExpr(const CVC4::Integer& value) :
    d_sexprType(SEXPR_INTEGER),
    d_integerValue(value),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  explicit SExpr(int value) :
    d_sexprType(SEXPR_INTEGER),
    d_integerValue(value),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  explicit SExpr(long int value) :
    d_sexprType(SEXPR_INTEGER),
    d_integerValue(value),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  explicit SExpr(unsigned int value) :
    d_sexprType(SEXPR_INTEGER),
    d_integerValue(value),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  explicit SExpr(unsigned long int value) :
    d_sexprType(SEXPR_INTEGER),
    d_integerValue(value),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  explicit SExpr(const CVC4::Rational& value) :
    d_sexprType(SEXPR_RATIONAL),
    d_integerValue(0),
    d_rationalValue(value),
    d_stringValue(""),
    d_children() {
  }

  explicit SExpr(const std::string& value) :
    d_sexprType(SEXPR_STRING),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value),
    d_children() {
  }

  /**
   * This constructs a string expression from a const char* value.
   * This cannot be removed in order to support SExpr("foo").
   * Given the other constructors this SExpr("foo") converts to bool.
   * instead of SExpr(string("foo")).
   */
  explicit SExpr(const char* value) :
    d_sexprType(SEXPR_STRING),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value),
    d_children() {
  }

  /**
   * This adds a convenience wrapper to SExpr to cast from bools.
   * This is internally handled as the strings "true" and "false"
   */
  explicit SExpr(bool value) :
    d_sexprType(SEXPR_KEYWORD),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value ? "true" : "false"),
    d_children() {
  }

  explicit SExpr(const Keyword& value) :
    d_sexprType(SEXPR_KEYWORD),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value.getString()),
    d_children() {
  }

  explicit SExpr(const std::vector<SExpr>& children) :
    d_sexprType(SEXPR_NOT_ATOM),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(""),
    d_children(children) {
  }

  /** Is this S-expression an atom? */
  bool isAtom() const {
    return d_sexprType != SEXPR_NOT_ATOM;
  }

  /** Is this S-expression an integer? */
  bool isInteger() const {
    return d_sexprType == SEXPR_INTEGER;
  }

  /** Is this S-expression a rational? */
  bool isRational() const {
    return d_sexprType == SEXPR_RATIONAL;
  }

  /** Is this S-expression a string? */
  bool isString() const {
    return d_sexprType == SEXPR_STRING;
  }

  /** Is this S-expression a keyword? */
  bool isKeyword() const {
    return d_sexprType == SEXPR_KEYWORD;
  }


  /**
   * Get the string value of this S-expression. This will cause an
   * error if this S-expression is not an atom.
   */
  std::string getValue() const;

  /**
   * Get the integer value of this S-expression. This will cause an
   * error if this S-expression is not an integer.
   */
  const CVC4::Integer& getIntegerValue() const;

  /**
   * Get the rational value of this S-expression. This will cause an
   * error if this S-expression is not a rational.
   */
  const CVC4::Rational& getRationalValue() const;

  /**
   * Get the children of this S-expression. This will cause an error
   * if this S-expression is not a list.
   */
  const std::vector<SExpr>& getChildren() const;

  /** Is this S-expression equal to another? */
  bool operator==(const SExpr& s) const;

  /** Is this S-expression different from another? */
  bool operator!=(const SExpr& s) const;


  /**
   * This returns the best match in the following order:
   * match atom with
   *  "true", "false" -> SExpr(value)
   * | is and integer -> as integer
   * | is a rational -> as rational
   * | _ -> SExpr()
   */
  static SExpr parseAtom(const std::string& atom);

  /**
   * Parses a list of atoms.
   */
  static SExpr parseListOfAtoms(const std::vector<std::string>& atoms);

  /**
   * Parses a list of list of atoms.
   */
  static SExpr parseListOfListOfAtoms(const std::vector< std::vector<std::string> >& atoms_lists);

};/* class SExpr */

}/* CVC4 namespace */

#endif /* __CVC4__SEXPR_H */
