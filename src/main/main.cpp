/*********************                                                        */
/*! \file main.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Christopher L. Conway
 ** Minor contributors (to current version): Clark Barrett, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Main driver for CVC4 executable
 **
 ** Main driver for CVC4 executable.
 **/
#include "main/main.h"

#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <unistd.h>

#include "base/output.h"
#include "expr/expr_manager.h"
#include "expr/statistics.h"
#include "main/command_executor.h"
#include "main/interactive_shell.h"
#include "options/language.h"
#include "options/main_options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/parser_exception.h"
#include "smt/smt_engine.h"
#include "smt_util/command.h"
#include "util/configuration.h"
#include "util/result.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::main;
using namespace CVC4::language;

/**
 * CVC4's main() routine is just an exception-safe wrapper around CVC4.
 * Please don't construct anything here.  Even if the constructor is
 * inside the try { }, an exception during destruction can cause
 * problems.  That's why main() wraps runCvc4() in the first place.
 * Put everything in runCvc4().
 */
int main(int argc, char* argv[]) {
  Options opts;
  try {
    return runCvc4(argc, argv, opts);
  } catch(OptionException& e) {
#ifdef CVC4_COMPETITION_MODE
    *opts[options::out] << "unknown" << endl;
#endif
    cerr << "CVC4 Error:" << endl << e << endl << endl
         << "Please use --help to get help on command-line options."
         << endl;
  } catch(Exception& e) {
#ifdef CVC4_COMPETITION_MODE
    *opts[options::out] << "unknown" << endl;
#endif
    if(opts[options::outputLanguage] == output::LANG_SMTLIB_V2_0 ||
       opts[options::outputLanguage] == output::LANG_SMTLIB_V2_5) {
      *opts[options::out] << "(error \"" << e << "\")" << endl;
    } else {
      *opts[options::err] << "CVC4 Error:" << endl << e << endl;
    }
    if(opts[options::statistics] && pExecutor != NULL) {
      pTotalTime->stop();
      pExecutor->flushStatistics(*opts[options::err]);
    }
  }
  exit(1);
}
