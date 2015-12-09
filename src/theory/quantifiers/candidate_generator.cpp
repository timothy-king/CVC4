/*********************                                                        */
/*! \file candidate_generator.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory uf candidate generator class
 **/

#include "options/quantifiers_options.h"
#include "theory/quantifiers/candidate_generator.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

bool CandidateGenerator::isLegalCandidate( Node n ){
  return ( !n.getAttribute(NoMatchAttribute()) && ( !options::cbqi() || !quantifiers::TermDb::hasInstConstAttr(n) ) );
}

void CandidateGeneratorQueue::addCandidate( Node n ) {
  if( isLegalCandidate( n ) ){
    d_candidates.push_back( n );
  }
}

void CandidateGeneratorQueue::reset( Node eqc ){
  if( d_candidate_index>0 ){
    d_candidates.erase( d_candidates.begin(), d_candidates.begin() + d_candidate_index );
    d_candidate_index = 0;
  }
  if( !eqc.isNull() ){
    d_candidates.push_back( eqc );
  }
}
Node CandidateGeneratorQueue::getNextCandidate(){
  if( d_candidate_index<(int)d_candidates.size() ){
    Node n = d_candidates[d_candidate_index];
    d_candidate_index++;
    return n;
  }else{
    d_candidate_index = 0;
    d_candidates.clear();
    return Node::null();
  }
}

CandidateGeneratorQE::CandidateGeneratorQE( QuantifiersEngine* qe, Node op ) :
  d_op( op ), d_qe( qe ), d_term_iter( -1 ){
  Assert( !d_op.isNull() );
}
void CandidateGeneratorQE::resetInstantiationRound(){
  d_term_iter_limit = d_qe->getTermDatabase()->getNumGroundTerms( d_op );
}

void CandidateGeneratorQE::reset( Node eqc ){
  d_term_iter = 0;
  if( eqc.isNull() ){
    d_mode = cand_term_db;
  }else{
    //create an equivalence class iterator in eq class eqc
    //d_qe->getEqualityQuery()->getEquivalenceClass( eqc, d_eqc );

    eq::EqualityEngine* ee = d_qe->getEqualityQuery()->getEngine();
    if( ee->hasTerm( eqc ) ){
      Node rep = ee->getRepresentative( eqc );
      d_eqc_iter = eq::EqClassIterator( rep, ee );
      d_mode = cand_term_eqc;
    }else{
      d_n = eqc;
      d_mode = cand_term_ident;
    }
    //a should be in its equivalence class
    //Assert( std::find( eqc.begin(), eqc.end(), a )!=eqc.end() );
  }
}
bool CandidateGeneratorQE::isLegalOpCandidate( Node n ) {
  if( n.hasOperator() ){
    if( isLegalCandidate( n ) ){
      return d_qe->getTermDatabase()->getOperator( n )==d_op;
    }
  }
  return false;
}

Node CandidateGeneratorQE::getNextCandidate(){
  if( d_mode==cand_term_db ){
    //get next candidate term in the uf term database
    while( d_term_iter<d_term_iter_limit ){
      Node n = d_qe->getTermDatabase()->getGroundTerm( d_op, d_term_iter );
      d_term_iter++;
      if( isLegalCandidate( n ) ){
        if( d_qe->getTermDatabase()->hasTermCurrent( n ) ){
          return n;
        }
      }
    }
  }else if( d_mode==cand_term_eqc ){
    while( !d_eqc_iter.isFinished() ){
      Node n = *d_eqc_iter;
      ++d_eqc_iter;
      if( isLegalOpCandidate( n ) ){
        return n;
      }
    }
  }else if( d_mode==cand_term_ident ){
    if( !d_n.isNull() ){
      Node n = d_n;
      d_n = Node::null();
      if( isLegalOpCandidate( n ) ){
        return n;
      }
    }
  }
  return Node::null();
}

CandidateGeneratorQELitEq::CandidateGeneratorQELitEq( QuantifiersEngine* qe, Node mpat ) :
  d_match_pattern( mpat ), d_qe( qe ){

}
void CandidateGeneratorQELitEq::resetInstantiationRound(){

}
void CandidateGeneratorQELitEq::reset( Node eqc ){
  d_eq = eq::EqClassesIterator( d_qe->getEqualityQuery()->getEngine() );
}
Node CandidateGeneratorQELitEq::getNextCandidate(){
  while( !d_eq.isFinished() ){
    Node n = (*d_eq);
    ++d_eq;
    if( n.getType().isComparableTo( d_match_pattern[0].getType() ) ){
      //an equivalence class with the same type as the pattern, return reflexive equality
      return NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), n, n );
    }
  }
  return Node::null();
}


CandidateGeneratorQELitDeq::CandidateGeneratorQELitDeq( QuantifiersEngine* qe, Node mpat ) :
  d_match_pattern( mpat ), d_qe( qe ){

  Assert( d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF );
  d_match_pattern_type = d_match_pattern[0].getType();
}

void CandidateGeneratorQELitDeq::resetInstantiationRound(){

}

void CandidateGeneratorQELitDeq::reset( Node eqc ){
  Node false_term = d_qe->getEqualityQuery()->getEngine()->getRepresentative( NodeManager::currentNM()->mkConst<bool>(false) );
  d_eqc_false = eq::EqClassIterator( false_term, d_qe->getEqualityQuery()->getEngine() );
}

Node CandidateGeneratorQELitDeq::getNextCandidate(){
  //get next candidate term in equivalence class
  while( !d_eqc_false.isFinished() ){
    Node n = (*d_eqc_false);
    ++d_eqc_false;
    if( n.getKind()==d_match_pattern.getKind() ){
      if( n[0].getType().isComparableTo( d_match_pattern_type ) ){
        //found an iff or equality, try to match it
        //DO_THIS: cache to avoid redundancies?
        //DO_THIS: do we need to try the symmetric equality for n?  or will it also exist in the eq class of false?
        return n;
      }
    }
  }
  return Node::null();
}


CandidateGeneratorQEAll::CandidateGeneratorQEAll( QuantifiersEngine* qe, Node mpat ) :
  d_match_pattern( mpat ), d_qe( qe ){
  d_match_pattern_type = mpat.getType();
  Assert( mpat.getKind()==INST_CONSTANT );
  d_f = quantifiers::TermDb::getInstConstAttr( mpat );
  d_index = mpat.getAttribute(InstVarNumAttribute());
}

void CandidateGeneratorQEAll::resetInstantiationRound() {

}

void CandidateGeneratorQEAll::reset( Node eqc ) {
  d_eq = eq::EqClassesIterator( d_qe->getEqualityQuery()->getEngine() );
  d_firstTime = true;
}

Node CandidateGeneratorQEAll::getNextCandidate() {
  while( !d_eq.isFinished() ){
    TNode n = (*d_eq);
    ++d_eq;
    if( n.getType().isComparableTo( d_match_pattern_type ) ){
      TNode nh = d_qe->getTermDatabase()->getEligibleTermInEqc( n );
      if( !nh.isNull() ){
        if( options::instMaxLevel()!=-1 || options::lteRestrictInstClosure() ){
          nh = d_qe->getEqualityQuery()->getInternalRepresentative( nh, d_f, d_index );
          //don't consider this if already the instantiation is ineligible
          if( !d_qe->getTermDatabase()->isTermEligibleForInstantiation( nh, d_f, false ) ){
            nh = Node::null();
          }
        }
        if( !nh.isNull() ){
          d_firstTime = false;
          //an equivalence class with the same type as the pattern, return it
          return nh;
        }
      }
    }
  }
  if( d_firstTime ){
    Assert( d_qe->getTermDatabase()->d_type_map[d_match_pattern_type].empty() );
    //must return something
    d_firstTime = false;
    return d_qe->getTermDatabase()->getModelBasisTerm( d_match_pattern_type );
  }
  return Node::null();
}
