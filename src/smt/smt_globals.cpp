/*********************                                                        */
/*! \file smt_globals.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2015  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This class is a light container for globals that used to live
 ** in options. This is NOT a good long term solution, but is a reasonable
 ** stop gap.
 **
 ** This class is a light container for globals that used to live
 ** in options. This is NOT a good long term solution, but is a reasonable
 ** stop gap.
 **/

#include "smt/smt_globals.h"

#include <cerrno>
#include <iostream>
#include <string>
#include <utility>

#include "cvc4autoconfig.h" // Needed for CVC4_REPLAY
#include "expr/expr_stream.h"
#include "options/open_ostream.h"
#include "options/option_exception.h"
#include "options/parser_options.h"
#include "smt_util/lemma_input_channel.h"
#include "smt_util/lemma_output_channel.h"

namespace CVC4 {

SmtGlobals::SmtGlobals()
    : d_lemmaInputChannel(NULL)
    , d_lemmaOutputChannel(NULL)
{}

SmtGlobals::~SmtGlobals(){}

void SmtGlobals::setLemmaInputChannel(LemmaInputChannel* in) {
  d_lemmaInputChannel = in;
}

void SmtGlobals::setLemmaOutputChannel(LemmaOutputChannel* out) {
  d_lemmaOutputChannel = out;
}


} /* namespace CVC4 */
