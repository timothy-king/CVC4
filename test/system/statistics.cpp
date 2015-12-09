/*********************                                                        */
/*! \file statistics.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple statistics test for CVC4.
 **
 ** This simple test just makes sure that the statistics interface is
 ** minimally functional.
 **/

#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "smt/smt_engine.h"
#include "util/statistics.h"
#include "printer/printer.h"

using namespace CVC4;
using namespace std;

int main() {
  ExprManager em;
  Options opts;
  SmtEngine smt(&em);
  smt.setOption("incremental", SExpr("true"));
  Expr x = em.mkVar("x", em.integerType());
  Expr y = em.mkVar("y", em.integerType());
  smt.assertFormula(em.mkExpr(kind::GT, em.mkExpr(kind::PLUS, x, y), em.mkConst(Rational(5))));
  Expr q = em.mkExpr(kind::GT, x, em.mkConst(Rational(0)));
  Result r = smt.query(q);

  if(r != Result::INVALID) {
    exit(1);
  }

  Statistics stats = smt.getStatistics();
  for(Statistics::iterator i = stats.begin(); i != stats.end(); ++i) {
    cout << "stat " << (*i).first << " is ";
#warning "Check this usage."
    Printer::getPrinter(Expr::setlanguage::getLanguage(cout))->toStream(cout, (*i).second);
    cout << endl;
  }

  smt.assertFormula(em.mkExpr(kind::LT, y, em.mkConst(Rational(5))));
  r = smt.query(q);
  Statistics stats2 = smt.getStatistics();
  bool different = false;
  for(Statistics::iterator i = stats2.begin(); i != stats2.end(); ++i) {
    cout << "stat1 " << (*i).first << " is ";
#warning "Check this usage."
    Printer::getPrinter(Expr::setlanguage::getLanguage(cout))->toStream(cout, stats.getStatistic((*i).first));
    cout << endl;
    cout << "stat2 " << (*i).first << " is ";
#warning "Check this usage."
    Printer::getPrinter(Expr::setlanguage::getLanguage(cout))->toStream(cout,(*i).second);
    cout << endl;
    if(smt.getStatistic((*i).first) != (*i).second) {
      cout << "SMT engine reports different value for statistic " << (*i).first << ": ";
#warning "Check this usage."
      Printer::getPrinter(Expr::setlanguage::getLanguage(cout))->toStream(cout, smt.getStatistic((*i).first));
      cout << endl;
      exit(1);
    }
    different = different || stats.getStatistic((*i).first) != (*i).second;
  }

#ifdef CVC4_STATISTICS_ON
  if(!different) {
    cout << "stats are the same!  bailing.." << endl;
    exit(1);
  }
#endif /* CVC4_STATISTICS_ON */

  return r == Result::VALID ? 0 : 1;
}
