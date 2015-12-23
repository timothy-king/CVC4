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

#include <cstdarg>
#include <cstdlib>
#include <exception>
#include <iosfwd>
#include <sstream>
#include <stdexcept>
#include <string>

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
                 const char* function, const char* tail);

  void construct(const char* header, const char* extra,
                 const char* function);


  /**
   * This is a convenience function for building usages that are variadic.
   *
   * Having IllegalArgumentException itself be variadic is problematic for
   * making sure calls to IllegalArgumentException clean up memory.
   */
  static std::string formatVaList(const char* format, va_list args);

  static std::string format_extra(const char* condStr, const char* argDesc);

  static char* s_header;

public:

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function, const char* fmt, va_list fmtArgs) :
    Exception() {

    construct(s_header, format_extra(condStr, argDesc).c_str(), function,
              formatVaList(fmt, fmtArgs).c_str());
  }

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function, const char* tail) :
    Exception() {
    construct(s_header, format_extra(condStr, argDesc).c_str(), function,
              tail);
  }

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function) :
    Exception() {
    construct(s_header, format_extra(condStr, argDesc).c_str(), function);
  }

  static std::string formatVariadic();
  static std::string formatVariadic(const char* format, ...);
};/* class IllegalArgumentException */

inline std::ostream& operator<<(std::ostream& os, const Exception& e) throw() CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const Exception& e) throw() {
  e.toStream(os);
  return os;
}

}/* CVC4 namespace */

//#if (defined(__BUILDING_CVC4LIB) || defined(__BUILDING_CVC4LIB_UNIT_TEST)) && !defined(__BUILDING_STATISTICS_FOR_EXPORT)
//#  include "base/cvc4_assert.h"
//#endif /* (__BUILDING_CVC4LIB || __BUILDING_CVC4LIB_UNIT_TEST) && !__BUILDING_STATISTICS_FOR_EXPORT */

namespace CVC4 {

template <class T> inline void CheckArgument(const char* condDesc, bool cond,
                                             const char* argDesc, const T& arg,
                                             const char* functionDesc,
                                             const char* fmt, ...) CVC4_PUBLIC;
template <class T> inline void CheckArgument(const char* condDesc, bool cond,
                                             const char* argDesc, const T& arg,
                                             const char* functionDesc,
                                             const char* fmt, ...) {
  if(__builtin_expect( ( !cond ), false )) {
    va_list fmtArgs;
    va_start(fmtArgs, fmt);
    //std::string tail = IllegalArgumentException::format_va_list(fmt, fmtArgs);
    ::CVC4::IllegalArgumentException exception(condDesc, argDesc, functionDesc, fmt, fmtArgs);
    va_end(fmtArgs);
    throw exception;
  }
}

template <class T> inline void CheckArgument(const char* condDesc, bool cond,
                                             const char* argDesc, const T& arg,
                                             const char* functionDesc
                                             ) CVC4_PUBLIC;
template <class T> inline void CheckArgument(const char* condDesc, bool cond,
                                             const char* argDesc, const T& arg,
                                             const char* functionDesc) {
  if(__builtin_expect( ( !cond ), false )) {
    throw ::CVC4::IllegalArgumentException(condDesc, argDesc, functionDesc);
  }
}

template <class T> inline void CheckArgument(bool cond, const T& arg,
                                             const char* fmt, ...) CVC4_PUBLIC;
template <class T> inline void CheckArgument(bool cond, const T& arg,
                                             const char* fmt, ...) {
  if(__builtin_expect( ( !cond ), false )) { \
    throw ::CVC4::IllegalArgumentException("", "", ""); \
  } \
}
template <class T> inline void CheckArgument(bool cond, const T& arg)
  CVC4_PUBLIC;
template <class T> inline void CheckArgument(bool cond, const T& arg) {
  if(__builtin_expect( ( !cond ), false )) { \
    throw ::CVC4::IllegalArgumentException("", "", ""); \
  } \
}


}/* CVC4 namespace */

#endif /* __CVC4__EXCEPTION_H */
