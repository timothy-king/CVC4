/*********************                                                        */
/*! \file ce_guided_instantiation.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_INSTANTIATION_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_INSTANTIATION_H

#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "options/quantifiers_modes.h"
#include "theory/quantifiers/ce_guided_single_inv.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** a synthesis conjecture */
class CegConjecture {
private:
  QuantifiersEngine * d_qe;
public:
  CegConjecture( QuantifiersEngine * qe, context::Context* c );
  /** quantified formula asserted */
  Node d_assert_quant;
  /** quantified formula (after processing) */
  Node d_quant;
  /** base instantiation */
  Node d_base_inst;
  /** expand base inst to disjuncts */
  std::vector< Node > d_base_disj;
  /** list of constants for quantified formula */
  std::vector< Node > d_candidates;
  /** list of variables on inner quantification */
  std::vector< Node > d_inner_vars;
  std::vector< std::vector< Node > > d_inner_vars_disj;
  /** list of terms we have instantiated candidates with */
  std::map< int, std::vector< Node > > d_candidate_inst;
  /** measure term */
  Node d_measure_term;
  /** measure sum size */
  int d_measure_term_size;
  /** refine count */
  unsigned d_refine_count;
  /** current extential quantifeirs whose couterexamples we must refine */
  std::vector< std::vector< Node > > d_ce_sk;
  /** single invocation utility */
  CegConjectureSingleInv * d_ceg_si;
public: //non-syntax guided (deprecated)
  /** guard */
  bool d_syntax_guided;
  Node d_nsg_guard;  
public:  //for fairness
  /** the cardinality literals */
  std::map< int, Node > d_lits;
  /** current cardinality */
  context::CDO< int > d_curr_lit;
  /** allocate literal */
  Node getLiteral( QuantifiersEngine * qe, int i );
  /** get guard */
  Node getGuard();
  /** is ground */
  bool isGround() { return d_inner_vars.empty(); }
  /** fairness */
  CegqiFairMode getCegqiFairMode();
  /** is single invocation */
  bool isSingleInvocation();
  /** is single invocation */
  bool isFullySingleInvocation();
  /** needs check */
  bool needsCheck( std::vector< Node >& lem );
  /** preregister conjecture */
  void preregisterConjecture( Node q );
  /** initialize guard */
  void initializeGuard( QuantifiersEngine * qe );
  /** assign */
  void assign( Node q );
  /** is assigned */
  bool isAssigned() { return !d_quant.isNull(); }
};


class CegInstantiation : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  /** the quantified formula stating the synthesis conjecture */
  CegConjecture * d_conj;
  /** last instantiation by single invocation module? */
  bool d_last_inst_si;
private: //for enforcing fairness
  /** measure functions */
  std::map< TypeNode, Node > d_uf_measure;
  /** register measured type */
  void registerMeasuredType( TypeNode tn );
  /** term -> size term */
  std::map< Node, Node > d_size_term;
  /** get size term */
  Node getSizeTerm( Node n, TypeNode tn, std::vector< Node >& lems );
  /** term x constructor -> lemma */
  std::map< Node, std::map< int, Node > > d_size_term_lemma;
  /** get measure lemmas */
  void getMeasureLemmas( Node n, Node v, std::vector< Node >& lems );
private:
  /** check conjecture */
  void checkCegConjecture( CegConjecture * conj );
  /** get model values */
  bool getModelValues( CegConjecture * conj, std::vector< Node >& n, std::vector< Node >& v );
  /** get model value */
  Node getModelValue( Node n );
  /** get model term */
  Node getModelTerm( Node n );
public:
  CegInstantiation( QuantifiersEngine * qe, context::Context* c );
public:
  bool needsCheck( Theory::Effort e );
  unsigned needsModel( Theory::Effort e );
  /* Call during quantifier engine's check */
  void check( Theory::Effort e, unsigned quant_e );
  /* Called for new quantifiers */
  void registerQuantifier( Node q );
  void assertNode( Node n );
  Node getNextDecisionRequest();
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const { return "CegInstantiation"; }
  /** print solution for synthesis conjectures */
  void printSynthSolution( std::ostream& out );
  /** collect disjuncts */
  static void collectDisjuncts( Node n, std::vector< Node >& ex );
  /** preregister assertion (before rewrite) */
  void preregisterAssertion( Node n );
public:
  class Statistics {
  public:
    IntStat d_cegqi_lemmas_ce;
    IntStat d_cegqi_lemmas_refine;
    IntStat d_cegqi_si_lemmas;
    Statistics();
    ~Statistics();
  };/* class CegInstantiation::Statistics */
  Statistics d_statistics;
};

}
}
}

#endif
