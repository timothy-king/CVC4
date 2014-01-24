/*********************                                                        */
/*! \file relevant_domain.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of relevant domain class
 **/

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

void RelevantDomain::RDomain::merge( RDomain * r ) {
  Assert( !d_parent );
  Assert( !r->d_parent );
  d_parent = r;
  for( unsigned i=0; i<d_terms.size(); i++ ){
    r->addTerm( d_terms[i] );
  }
  d_terms.clear();
}

void RelevantDomain::RDomain::addTerm( Node t ) {
  if( std::find( d_terms.begin(), d_terms.end(), t )==d_terms.end() ){
    d_terms.push_back( t );
  }
}

RelevantDomain::RDomain * RelevantDomain::RDomain::getParent() {
  if( !d_parent ){
    return this;
  }else{
    RDomain * p = d_parent->getParent();
    d_parent = p;
    return p;
  }
}

void RelevantDomain::RDomain::removeRedundantTerms( FirstOrderModel * fm ) {
  std::map< Node, Node > rterms;
  for( unsigned i=0; i<d_terms.size(); i++ ){
    Node r = d_terms[i];
    if( !TermDb::hasInstConstAttr( d_terms[i] ) ){
      r = fm->getRepresentative( d_terms[i] );
    }
    if( rterms.find( r )==rterms.end() ){
      rterms[r] = d_terms[i];
    }
  }
  d_terms.clear();
  for( std::map< Node, Node >::iterator it = rterms.begin(); it != rterms.end(); ++it ){
    d_terms.push_back( it->second );
  }
}



RelevantDomain::RelevantDomain( QuantifiersEngine* qe, FirstOrderModel* m ) : d_qe( qe ), d_model( m ){

}

RelevantDomain::RDomain * RelevantDomain::getRDomain( Node n, int i ) {
  if( d_rel_doms.find( n )==d_rel_doms.end() || d_rel_doms[n].find( i )==d_rel_doms[n].end() ){
    d_rel_doms[n][i] = new RDomain;
    d_rn_map[d_rel_doms[n][i]] = n;
    d_ri_map[d_rel_doms[n][i]] = i;
  }
  return d_rel_doms[n][i]->getParent();
}

void RelevantDomain::compute(){
  for( std::map< Node, std::map< int, RDomain * > >::iterator it = d_rel_doms.begin(); it != d_rel_doms.end(); ++it ){
    for( std::map< int, RDomain * >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
      it2->second->reset();
    }
  }
  for( int i=0; i<(int)d_model->getNumAssertedQuantifiers(); i++ ){
    Node f = d_model->getAssertedQuantifier( i );
    Node icf = d_qe->getTermDatabase()->getInstConstantBody( f );
    Trace("rel-dom-debug") << "compute relevant domain for " << icf << std::endl;
    computeRelevantDomain( icf, true, true );
  }

  Trace("rel-dom-debug") << "account for ground terms" << std::endl;
  for( std::map< Node, std::vector< Node > >::iterator it = d_model->d_uf_terms.begin(); it != d_model->d_uf_terms.end(); ++it ){
    Node op = it->first;
    for( unsigned i=0; i<it->second.size(); i++ ){
      Node n = it->second[i];
      //if it is a non-redundant term
      if( !n.getAttribute(NoMatchAttribute()) ){
        for( unsigned j=0; j<n.getNumChildren(); j++ ){
          RDomain * rf = getRDomain( op, j );
          rf->addTerm( n[j] );
        }
      }
    }
  }
  //print debug
  for( std::map< Node, std::map< int, RDomain * > >::iterator it = d_rel_doms.begin(); it != d_rel_doms.end(); ++it ){
    Trace("rel-dom") << "Relevant domain for " << it->first << " : " << std::endl;
    for( std::map< int, RDomain * >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
      Trace("rel-dom") << "   " << it2->first << " : ";
      RDomain * r = it2->second;
      RDomain * rp = r->getParent();
      if( r==rp ){
        r->removeRedundantTerms( d_model );
        for( unsigned i=0; i<r->d_terms.size(); i++ ){
          Trace("rel-dom") << r->d_terms[i] << " ";
        }
      }else{
        Trace("rel-dom") << "Dom( " << d_rn_map[rp] << ", " << d_ri_map[rp] << " ) ";
      }
      Trace("rel-dom") << std::endl;
    }
  }

}

void RelevantDomain::computeRelevantDomain( Node n, bool hasPol, bool pol ) {

  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( n.getKind()==APPLY_UF ){
      RDomain * rf = getRDomain( n.getOperator(), i );
      if( n[i].getKind()==INST_CONSTANT ){
        Node q = d_qe->getTermDatabase()->getInstConstAttr( n[i] );
        //merge the RDomains
        unsigned id = n[i].getAttribute(InstVarNumAttribute());
        Trace("rel-dom-debug") << n[i] << " is variable # " << id << " for " << q;
        Trace("rel-dom-debug") << " with body : " << d_qe->getTermDatabase()->getInstConstantBody( q ) << std::endl;
        RDomain * rq = getRDomain( q, id );
        if( rf!=rq ){
          rq->merge( rf );
        }
      }else{
        //term to add
        rf->addTerm( n[i] );
      }
    }

    //TODO
    if( n[i].getKind()!=FORALL ){
      bool newHasPol = hasPol;
      bool newPol = pol;
      computeRelevantDomain( n[i], newHasPol, newPol );
    }
  }
}

Node RelevantDomain::getRelevantTerm( Node f, int i, Node r ) {
  RDomain * rf = getRDomain( f, i );
  Trace("rel-dom-debug") << "Get relevant domain " << rf << " " << r << std::endl;
  if( !d_qe->getEqualityQuery()->getEngine()->hasTerm( r ) || rf->hasTerm( r ) ){
    return r;
  }else{
    Node rr = d_model->getRepresentative( r );
    eq::EqClassIterator eqc( rr, d_qe->getEqualityQuery()->getEngine() );
    while( !eqc.isFinished() ){
      Node en = (*eqc);
      if( rf->hasTerm( en ) ){
        return en;
      }
      ++eqc;
    }
    //otherwise, may be equal to some non-ground term

    return r;
  }
}
