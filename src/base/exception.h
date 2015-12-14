/*********************                                                        */
/*! \file exception.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief CVC4's exception base class and some associated utilities
 **
 ** CVC4's exception base class and some associated utilities.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__EXCEPTION_H
#define __CVC4__EXCEPTION_H

#include <iostream>
#include <string>
#include <sstream>
#include <stdexcept>
#include <exception>
#include <cstdlib>
#include <cstdarg>

#include "base/cvc4_assert.h"

namespace CVC4 {

class CVC4_PUBLIC Exception : public std::exception {
protected:
  std::string d_msg;

public:
  // Constructors
  Exception() throw() : d_msg("Unknown exception") {}
  Exception(const std::string& msg) throw() : d_msg(msg) {}
  Exception(const char* msg) throw() : d_msg(msg) {}

  // Destructor
  virtual ~Exception() throw() {}

  // NON-VIRTUAL METHOD for setting and printing the error message
  void setMessage(const std::string& msg) throw() { d_msg = msg; }
  std::string getMessage() const throw() { return d_msg; }

  // overridden from base class std::exception
  virtual const char* what() const throw() { return d_msg.c_str(); }

  /**
   * Get this exception as a string.  Note that
   *   cout << ex.toString();
   * is subtly different from
   *   cout << ex;
   * which is equivalent to
   *   ex.toStream(cout);
   * That is because with the latter two, the output language (and
   * other preferences) for exprs on the stream is respected.  In
   * toString(), there is no stream, so the parameters are default
   * and you'll get exprs and types printed using the AST language.
   */
  std::string toString() const throw() {
    std::stringstream ss;
    toStream(ss);
    return ss.str();
  }

  /**
   * Printing: feel free to redefine toStream().  When overridden in
   * a derived class, it's recommended that this method print the
   * type of exception before the actual message.
   */
  virtual void toStream(std::ostream& os) const throw() { os << d_msg; }

};/* class Exception */

class CVC4_PUBLIC IllegalArgumentException : public Exception {
protected:
  IllegalArgumentException() : Exception() {}

  void construct(const char* header, const char* extra,
                 const char* function, const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    construct(header, extra, function, fmt, args);
    va_end(args);
  }

  void construct(const char* header, const char* extra,
                 const char* function, const char* fmt, va_list args);

  void construct(const char* header, const char* extra,
                 const char* function);

public:
  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function, const char* fmt, ...) :
    Exception() {
    va_list args;
    va_start(args, fmt);
    construct("Illegal argument detected",
              ( std::string("`") + argDesc + "' is a bad argument"
                + (*condStr == '\0' ? std::string() :
                    ( std::string("; expected ") +
                        condStr + " to hold" )) ).c_str(),
              function, fmt, args);
    va_end(args);
  }

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function) :
    Exception() {
    construct("Illegal argument detected",
              ( std::string("`") + argDesc + "' is a bad argument"
                + (*condStr == '\0' ? std::string() :
                    ( std::string("; expected ") +
                        condStr + " to hold" )) ).c_str(),
              function);
  }
};/* class IllegalArgumentException */

inline std::ostream& operator<<(std::ostream& os, const Exception& e) throw() CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const Exception& e) throw() {
  e.toStream(os);
  return os;
}

}/* CVC4 namespace */

#endif /* __CVC4__EXCEPTION_H */
