/*********************                                                        */
/*! \file ce_guided_single_inv_ei.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief utility for inferring entailments for cegqi
 **
 **/

#include "options/quantifiers_options.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/ce_guided_single_inv_ei.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/theory_engine.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

CegEntailmentInfer::CegEntailmentInfer( QuantifiersEngine * qe, SingleInvocationPartition * sip ) : d_qe( qe ), d_sip( sip ) {

}

bool CegEntailmentInfer::getEntailedConjecture( Node& conj, Node& exp ) {
  if( Trace.isOn("cegqi-ei") ){
    Trace("cegqi-ei") << "Infer new conjecture from : " << std::endl;
    d_sip->debugPrint( "cegqi-ei" );
    Trace("cegqi-ei") << "Current assertions : " << std::endl;
    d_qe->getTheoryEngine()->printAssertions("cegqi-ei");
  }
  
  
  return false;
}

}
