/*********************                                                        */
/*! \file term_database.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Francois Bobot
 ** Minor contributors (to current version): Kshitij Bansal, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of term databse class
 **/

#include "options/quantifiers_options.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fun_def_engine.h"
#include "theory/quantifiers/rewrite_engine.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/quantifiers/trigger.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "util/datatype.h"

//for sygus
#include "base/bitvector.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/theory_bv_utils.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

using namespace CVC4::theory::inst;

TNode TermArgTrie::existsTerm( std::vector< TNode >& reps, int argIndex ) {
  if( argIndex==(int)reps.size() ){
    if( d_data.empty() ){
      return Node::null();
    }else{
      return d_data.begin()->first;
    }
  }else{
    std::map< TNode, TermArgTrie >::iterator it = d_data.find( reps[argIndex] );
    if( it==d_data.end() ){
      return Node::null();
    }else{
      return it->second.existsTerm( reps, argIndex+1 );
    }
  }
}

bool TermArgTrie::addTerm( TNode n, std::vector< TNode >& reps, int argIndex ){
  if( argIndex==(int)reps.size() ){
    if( d_data.empty() ){
      //store n in d_data (this should be interpretted as the "data" and not as a reference to a child)
      d_data[n].clear();
      return true;
    }else{
      return false;
    }
  }else{
    return d_data[reps[argIndex]].addTerm( n, reps, argIndex+1 );
  }
}

void TermArgTrie::debugPrint( const char * c, Node n, unsigned depth ) {
  for( std::map< TNode, TermArgTrie >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
    for( unsigned i=0; i<depth; i++ ){ Debug(c) << "  "; }
    Debug(c) << it->first << std::endl;
    it->second.debugPrint( c, n, depth+1 );
  }
}

TermDb::TermDb( context::Context* c, context::UserContext* u, QuantifiersEngine* qe ) : d_quantEngine( qe ), d_op_id_count( 0 ), d_typ_id_count( 0 ) {
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  d_zero = NodeManager::currentNM()->mkConst( Rational( 0 ) );
  d_one = NodeManager::currentNM()->mkConst( Rational( 1 ) );
  if( options::ceGuidedInst() ){
    d_sygus_tdb = new TermDbSygus;
  }else{
    d_sygus_tdb = NULL;
  }
}

/** ground terms */
unsigned TermDb::getNumGroundTerms( Node f ) {
  std::map< Node, std::vector< Node > >::iterator it = d_op_map.find( f );
  if( it!=d_op_map.end() ){
    return it->second.size();
  }else{
    return 0;
  }
}

Node TermDb::getGroundTerm( Node f, unsigned i ) {
  Assert( i<d_op_map[f].size() );
  return d_op_map[f][i];
}

Node TermDb::getOperator( Node n ) {
  //return n.getOperator();
  Kind k = n.getKind();
  if( k==SELECT || k==STORE || k==UNION || k==INTERSECTION || k==SUBSET || k==SETMINUS || k==MEMBER || k==SINGLETON ){
    //since it is parametric, use a particular one as op
    TypeNode tn = n[0].getType();
    Node op = n.getOperator();
    std::map< Node, std::map< TypeNode, Node > >::iterator ito = d_par_op_map.find( op );
    if( ito!=d_par_op_map.end() ){
      std::map< TypeNode, Node >::iterator it = ito->second.find( tn );
      if( it!=ito->second.end() ){
        return it->second;
      }
    }
    d_par_op_map[op][tn] = n;
    return n;
  }else if( inst::Trigger::isAtomicTriggerKind( k ) ){
    return n.getOperator();
  }else{
    return Node::null();
  }
}

void TermDb::addTerm( Node n, std::set< Node >& added, bool withinQuant, bool withinInstClosure ){
  //don't add terms in quantifier bodies
  if( withinQuant && !options::registerQuantBodyTerms() ){
    return;
  }else{
    bool rec = false;
    if( d_processed.find( n )==d_processed.end() ){
      d_processed.insert(n);
      if( !TermDb::hasInstConstAttr(n) ){
        Trace("term-db-debug") << "register term : " << n << std::endl;
        d_type_map[ n.getType() ].push_back( n );
        //if this is an atomic trigger, consider adding it
        if( inst::Trigger::isAtomicTrigger( n ) ){
          Trace("term-db") << "register term in db " << n << std::endl;
          Node op = getOperator( n );
          d_op_map[op].push_back( n );
          added.insert( n );

          if( options::eagerInstQuant() ){
            for( unsigned i=0; i<n.getNumChildren(); i++ ){
              if( !n.hasAttribute(InstLevelAttribute()) && n.getAttribute(InstLevelAttribute())==0 ){
                int addedLemmas = 0;
                for( unsigned i=0; i<d_op_triggers[op].size(); i++ ){
                  addedLemmas += d_op_triggers[op][i]->addTerm( n );
                }
              }
            }
          }
        }
      }
      rec = true;
    }
    if( withinInstClosure && d_iclosure_processed.find( n )==d_iclosure_processed.end() ){
      d_iclosure_processed.insert( n );
      rec = true;
    }
    if( rec && n.getKind()!=FORALL ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        addTerm( n[i], added, withinQuant, withinInstClosure );
      }
    }
  }
}

void TermDb::computeArgReps( TNode n ) {
  if( d_arg_reps.find( n )==d_arg_reps.end() ){
    eq::EqualityEngine * ee = d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
    for( unsigned j=0; j<n.getNumChildren(); j++ ){
      TNode r = ee->hasTerm( n[j] ) ? ee->getRepresentative( n[j] ) : n[j];
      d_arg_reps[n].push_back( r );
    }
  }
}

void TermDb::computeUfEqcTerms( TNode f ) {
  if( d_func_map_eqc_trie.find( f )==d_func_map_eqc_trie.end() ){
    d_func_map_eqc_trie[f].clear();
    eq::EqualityEngine * ee = d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
    for( unsigned i=0; i<d_op_map[f].size(); i++ ){
      TNode n = d_op_map[f][i];
      if( hasTermCurrent( n ) ){
        if( !n.getAttribute(NoMatchAttribute()) ){
          computeArgReps( n );
          TNode r = ee->hasTerm( n ) ? ee->getRepresentative( n ) : n;
          d_func_map_eqc_trie[f].d_data[r].addTerm( n, d_arg_reps[n] );
        }
      }
    }
  }
}

TNode TermDb::evaluateTerm( TNode n, std::map< TNode, TNode >& subs, bool subsRep ) {
  Trace("term-db-eval") << "evaluate term : " << n << std::endl;
  eq::EqualityEngine * ee = d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
  if( ee->hasTerm( n ) ){
    Trace("term-db-eval") << "...exists in ee, return rep " << std::endl;
    return ee->getRepresentative( n );
  }else if( n.getKind()==BOUND_VARIABLE ){
    Assert( subs.find( n )!=subs.end() );
    Trace("term-db-eval") << "...substitution is : " << subs[n] << std::endl;
    if( subsRep ){
      Assert( ee->hasTerm( subs[n] ) );
      Assert( ee->getRepresentative( subs[n] )==subs[n] );
      return subs[n];
    }else{
      return evaluateTerm( subs[n], subs, subsRep );
    }
  }else{
    if( n.hasOperator() ){
      TNode f = getOperator( n );
      if( !f.isNull() ){
        std::vector< TNode > args;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          TNode c = evaluateTerm( n[i], subs, subsRep );
          if( c.isNull() ){
            return TNode::null();
          }
          Trace("term-db-eval") << "Got child : " << c << std::endl;
          args.push_back( c );
        }
        Trace("term-db-eval") << "Get term from DB" << std::endl;
        TNode nn = d_func_map_trie[f].existsTerm( args );
        Trace("term-db-eval") << "Got term " << nn << std::endl;
        if( !nn.isNull() ){
          if( ee->hasTerm( nn ) ){
            Trace("term-db-eval") << "return rep " << std::endl;
            return ee->getRepresentative( nn );
          }else{
            //Assert( false );
          }
        }
      }
    }
    return TNode::null();
  }
}

TNode TermDb::evaluateTerm( TNode n ) {
  eq::EqualityEngine * ee = d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
  if( ee->hasTerm( n ) ){
    return ee->getRepresentative( n );
  }else if( n.getKind()!=BOUND_VARIABLE ){
    if( n.hasOperator() ){
      TNode f = getOperator( n );
      if( !f.isNull() ){
        std::vector< TNode > args;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          TNode c = evaluateTerm( n[i] );
          if( c.isNull() ){
            return TNode::null();
          }
          args.push_back( c );
        }
        TNode nn = d_func_map_trie[f].existsTerm( args );
        if( !nn.isNull() ){
          if( ee->hasTerm( nn ) ){
            return ee->getRepresentative( nn );
          }else{
            //Assert( false );
          }
        }
      }
    }
  }
  return TNode::null();
}

bool TermDb::isEntailed( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool pol ) {
  Trace("term-db-eval") << "Check entailed : " << n << ", pol = " << pol << std::endl;
  Assert( n.getType().isBoolean() );
  if( n.getKind()==EQUAL ){
    TNode n1 = evaluateTerm( n[0], subs, subsRep );
    if( !n1.isNull() ){
      TNode n2 = evaluateTerm( n[1], subs, subsRep );
      if( !n2.isNull() ){
        eq::EqualityEngine * ee = d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
        Assert( ee->hasTerm( n1 ) );
        Assert( ee->hasTerm( n2 ) );
        if( pol ){
          return n1==n2 || ee->areEqual( n1, n2 );
        }else{
          return n1!=n2 && ee->areDisequal( n1, n2, false );
        }
      }
    }
  }else if( n.getKind()==APPLY_UF ){
    TNode n1 = evaluateTerm( n, subs, subsRep );
    if( !n1.isNull() ){
      eq::EqualityEngine * ee = d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
      Assert( ee->hasTerm( n1 ) );
      TNode n2 = pol ? d_true : d_false;
      if( ee->hasTerm( n2 ) ){
        return ee->areEqual( n1, n2 );
      }
    }
  }else if( n.getKind()==NOT ){
    return isEntailed( n[0], subs, subsRep, !pol );
  }else if( n.getKind()==OR || n.getKind()==AND ){
    bool simPol = ( pol && n.getKind()==OR ) || ( !pol && n.getKind()==AND );
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( isEntailed( n[i], subs, subsRep, pol ) ){
        if( simPol ){
          return true;
        }
      }else{
        if( !simPol ){
          return false;
        }
      }
    }
    return !simPol;
  }else if( n.getKind()==IFF || n.getKind()==ITE ){
    for( unsigned i=0; i<2; i++ ){
      if( isEntailed( n[0], subs, subsRep, i==0 ) ){
        unsigned ch = ( n.getKind()==IFF || i==0 ) ? 1 : 2;
        bool reqPol = ( n.getKind()==ITE || i==0 ) ? pol : !pol;
        return isEntailed( n[ch], subs, subsRep, reqPol );
      }
    }
  }
  return false;
}

bool TermDb::hasTermCurrent( Node n, bool useMode ) {
  if( !useMode ){
    return d_has_map.find( n )!=d_has_map.end();
  }else{
    //return d_quantEngine->getMasterEqualityEngine()->hasTerm( n ); //some assertions are not sent to EE
    if( options::termDbMode()==TERM_DB_ALL ){
      return true;
    }else if( options::termDbMode()==TERM_DB_RELEVANT ){
      return d_has_map.find( n )!=d_has_map.end();
    }else{
      Assert( false );
      return false;
    }
  }
}

bool TermDb::isTermEligibleForInstantiation( TNode n, TNode f, bool print ) {
  if( options::lteRestrictInstClosure() ){
    //has to be both in inst closure and in ground assertions
    if( !isInstClosure( n ) ){
      Trace("inst-add-debug") << "Term " << n << " is not an inst-closure term." << std::endl;
      return false;
    }
    // hack : since theories preregister terms not in assertions, we are using hasTermCurrent to approximate this
    if( !hasTermCurrent( n, false ) ){
      Trace("inst-add-debug") << "Term " << n << " is not in a ground assertion." << std::endl;
      return false;
    }
  }
  if( options::instMaxLevel()!=-1 ){
    if( n.hasAttribute(InstLevelAttribute()) ){
      int fml = f.isNull() ? -1 : getQAttrQuantInstLevel( f );
      unsigned ml = fml>=0 ? fml : options::instMaxLevel();

      if( n.getAttribute(InstLevelAttribute())>ml ){
        Trace("inst-add-debug") << "Term " << n << " has instantiation level " << n.getAttribute(InstLevelAttribute());
        Trace("inst-add-debug") << ", which is more than maximum allowed level " << ml << " for this quantified formula." << std::endl;
        return false;
      }
    }else{
      if( options::instLevelInputOnly() ){
        Trace("inst-add-debug") << "Term " << n << " does not have an instantiation level." << std::endl;
        return false;
      }
    }
  }
  return true;
}

Node TermDb::getEligibleTermInEqc( TNode r ) {
  if( isTermEligibleForInstantiation( r, TNode::null() ) ){
    return r;
  }else{
    std::map< Node, Node >::iterator it = d_term_elig_eqc.find( r );
    if( it==d_term_elig_eqc.end() ){
      Node h;
      eq::EqualityEngine* ee = d_quantEngine->getMasterEqualityEngine();
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
      while( h.isNull() && !eqc_i.isFinished() ){
        TNode n = (*eqc_i);
        ++eqc_i;
        if( hasTermCurrent( n ) ){
          h = n;
        }
      }
      d_term_elig_eqc[r] = h;
      return h;
    }else{
      return it->second;
    }
  }
}

bool TermDb::isInstClosure( Node r ) {
  return d_iclosure_processed.find( r )!=d_iclosure_processed.end();
}

void TermDb::setHasTerm( Node n ) {
  Trace("term-db-debug2") << "hasTerm : " << n  << std::endl;
  //if( inst::Trigger::isAtomicTrigger( n ) ){
  if( d_has_map.find( n )==d_has_map.end() ){
    d_has_map[n] = true;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      setHasTerm( n[i] );
    }
  }
}

void TermDb::presolve() {
  if( options::incrementalSolving() ){
    //reset the caches that are SAT context-independent
    d_op_map.clear();
    d_type_map.clear();
    d_processed.clear();
    d_iclosure_processed.clear();
  }
}

void TermDb::reset( Theory::Effort effort ){
  int nonCongruentCount = 0;
  int congruentCount = 0;
  int alreadyCongruentCount = 0;
  int nonRelevantCount = 0;
  d_op_nonred_count.clear();
  d_arg_reps.clear();
  d_func_map_trie.clear();
  d_func_map_eqc_trie.clear();

  eq::EqualityEngine* ee = d_quantEngine->getMasterEqualityEngine();
  //compute has map
  if( options::termDbMode()==TERM_DB_RELEVANT || options::lteRestrictInstClosure() ){
    d_has_map.clear();
    d_term_elig_eqc.clear();
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      bool addedFirst = false;
      Node first;
      //TODO: ignoring singleton eqc isn't enough, need to ensure eqc are relevant
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
      while( !eqc_i.isFinished() ){
        TNode n = (*eqc_i);
        if( first.isNull() ){
          first = n;
        }else{
          if( !addedFirst ){
            addedFirst = true;
            setHasTerm( first );
          }
          setHasTerm( n );
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
      Theory* theory = d_quantEngine->getTheoryEngine()->d_theoryTable[theoryId];
      if (theory && d_quantEngine->getTheoryEngine()->d_logicInfo.isTheoryEnabled(theoryId)) {
        context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
        for (unsigned i = 0; it != it_end; ++ it, ++i) {
          if( (*it).assertion.getKind()!=INST_CLOSURE ){
            setHasTerm( (*it).assertion );
          }
        }
      }
    }
  }


  //rebuild d_func/pred_map_trie for each operation, this will calculate all congruent terms
  for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
    d_op_nonred_count[ it->first ] = 0;
    Trace("term-db-debug") << "Adding terms for operator " << it->first << std::endl;
    for( unsigned i=0; i<it->second.size(); i++ ){
      Node n = it->second[i];
      //to be added to term index, term must be relevant, and either exist in EE or be an inst closure term
      if( hasTermCurrent( n ) && ( ee->hasTerm( n ) || d_iclosure_processed.find( n )!=d_iclosure_processed.end() ) ){
        if( !n.getAttribute(NoMatchAttribute()) ){
          if( options::finiteModelFind() ){
            computeModelBasisArgAttribute( n );
          }
          computeArgReps( n );

          if( Trace.isOn("term-db-debug") ){
            Trace("term-db-debug") << "Adding term " << n << " with arg reps : ";
            for( unsigned i=0; i<d_arg_reps[n].size(); i++ ){
              Trace("term-db-debug") << d_arg_reps[n] << " ";
            }
            Trace("term-db-debug") << std::endl;
          }

          if( !d_func_map_trie[ it->first ].addTerm( n, d_arg_reps[n] ) ){
            NoMatchAttribute nma;
            n.setAttribute(nma,true);
            Trace("term-db-debug") << n << " is redundant." << std::endl;
            congruentCount++;
          }else{
            nonCongruentCount++;
            d_op_nonred_count[ it->first ]++;
          }
        }else{
          congruentCount++;
          alreadyCongruentCount++;
        }
      }else{
        Trace("term-db-debug") << n << " is not relevant." << std::endl;
        nonRelevantCount++;
      }
    }
  }
  Trace("term-db-stats") << "TermDb: Reset" << std::endl;
  Trace("term-db-stats") << "Non-Congruent/Congruent/Non-Relevant = ";
  Trace("term-db-stats") << nonCongruentCount << " / " << congruentCount << " (" << alreadyCongruentCount << ") / " << nonRelevantCount << std::endl;
  if( Debug.isOn("term-db") ){
    Debug("term-db") << "functions : " << std::endl;
    for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
      if( it->second.size()>0 ){
        Debug("term-db") << "- " << it->first << std::endl;
        d_func_map_trie[ it->first ].debugPrint("term-db", it->second[0]);
      }
    }
  }
}

TermArgTrie * TermDb::getTermArgTrie( Node f ) {
  std::map< Node, TermArgTrie >::iterator itut = d_func_map_trie.find( f );
  if( itut!=d_func_map_trie.end() ){
    return &itut->second;
  }else{
    return NULL;
  }
}

TermArgTrie * TermDb::getTermArgTrie( Node eqc, Node f ) {
  computeUfEqcTerms( f );
  std::map< Node, TermArgTrie >::iterator itut = d_func_map_eqc_trie.find( f );
  if( itut==d_func_map_eqc_trie.end() ){
    return NULL;
  }else{
    if( eqc.isNull() ){
      return &itut->second;
    }else{
      std::map< TNode, TermArgTrie >::iterator itute = itut->second.d_data.find( eqc );
      if( itute!=itut->second.d_data.end() ){
        return &itute->second;
      }else{
        return NULL;
      }
    }
  }
}

TNode TermDb::existsTerm( Node f, Node n ) {
  computeArgReps( n );
  return d_func_map_trie[f].existsTerm( d_arg_reps[n] );
}

Node TermDb::getModelBasisTerm( TypeNode tn, int i ){
  if( d_model_basis_term.find( tn )==d_model_basis_term.end() ){
    Node mbt;
    if( tn.isInteger() || tn.isReal() ){
      mbt = d_zero;
    }else if( isClosedEnumerableType( tn ) ){
      mbt = tn.mkGroundTerm();
    }else{
      if( options::fmfFreshDistConst() || d_type_map[ tn ].empty() ){
        std::stringstream ss;
        ss << Expr::setlanguage(options::outputLanguage());
        ss << "e_" << tn;
        mbt = NodeManager::currentNM()->mkSkolem( ss.str(), tn, "is a model basis term" );
        Trace("mkVar") << "ModelBasis:: Make variable " << mbt << " : " << tn << std::endl;
        if( options::instMaxLevel()!=-1 ){
          QuantifiersEngine::setInstantiationLevelAttr( mbt, 0 );
        }
      }else{
        mbt = d_type_map[ tn ][ 0 ];
      }
    }
    ModelBasisAttribute mba;
    mbt.setAttribute(mba,true);
    d_model_basis_term[tn] = mbt;
    Trace("model-basis-term") << "Choose " << mbt << " as model basis term for " << tn << std::endl;
  }
  return d_model_basis_term[tn];
}

Node TermDb::getModelBasisOpTerm( Node op ){
  if( d_model_basis_op_term.find( op )==d_model_basis_op_term.end() ){
    TypeNode t = op.getType();
    std::vector< Node > children;
    children.push_back( op );
    for( int i=0; i<(int)(t.getNumChildren()-1); i++ ){
      children.push_back( getModelBasisTerm( t[i] ) );
    }
    if( children.size()==1 ){
      d_model_basis_op_term[op] = op;
    }else{
      d_model_basis_op_term[op] = NodeManager::currentNM()->mkNode( APPLY_UF, children );
    }
  }
  return d_model_basis_op_term[op];
}

Node TermDb::getModelBasis( Node q, Node n ){
  //make model basis
  if( d_model_basis_terms.find( q )==d_model_basis_terms.end() ){
    for( unsigned j=0; j<q[0].getNumChildren(); j++ ){
      d_model_basis_terms[q].push_back( getModelBasisTerm( q[0][j].getType() ) );
    }
  }
  Node gn = n.substitute( d_inst_constants[q].begin(), d_inst_constants[q].end(),
                          d_model_basis_terms[q].begin(), d_model_basis_terms[q].end() );
  return gn;
}

Node TermDb::getModelBasisBody( Node q ){
  if( d_model_basis_body.find( q )==d_model_basis_body.end() ){
    Node n = getInstConstantBody( q );
    d_model_basis_body[q] = getModelBasis( q, n );
  }
  return d_model_basis_body[q];
}

void TermDb::computeModelBasisArgAttribute( Node n ){
  if( !n.hasAttribute(ModelBasisArgAttribute()) ){
    //ensure that the model basis terms have been defined
    if( n.getKind()==APPLY_UF ){
      getModelBasisOpTerm( n.getOperator() );
    }
    uint64_t val = 0;
    //determine if it has model basis attribute
    for( unsigned j=0; j<n.getNumChildren(); j++ ){
      if( n[j].getAttribute(ModelBasisAttribute()) ){
        val++;
      }
    }
    ModelBasisArgAttribute mbaa;
    n.setAttribute( mbaa, val );
  }
}

void TermDb::makeInstantiationConstantsFor( Node q ){
  if( d_inst_constants.find( q )==d_inst_constants.end() ){
    Debug("quantifiers-engine") << "Instantiation constants for " << q << " : " << std::endl;
    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
      d_vars[q].push_back( q[0][i] );
      //make instantiation constants
      Node ic = NodeManager::currentNM()->mkInstConstant( q[0][i].getType() );
      d_inst_constants_map[ic] = q;
      d_inst_constants[ q ].push_back( ic );
      Debug("quantifiers-engine") << "  " << ic << std::endl;
      //set the var number attribute
      InstVarNumAttribute ivna;
      ic.setAttribute( ivna, i );
      InstConstantAttribute ica;
      ic.setAttribute( ica, q );
      //also set the no-match attribute
      NoMatchAttribute nma;
      ic.setAttribute(nma,true);
    }
  }
}

void TermDb::getBoundVars2( Node n, std::vector< Node >& vars, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==BOUND_VARIABLE ){
      if( std::find( vars.begin(), vars.end(), n )==vars.end() ) {
        vars.push_back( n );
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getBoundVars2( n[i], vars, visited );
    }
  }
}

Node TermDb::getRemoveQuantifiers2( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator it = visited.find( n );
  if( it!=visited.end() ){
    return it->second;
  }else{
    Node ret = n;
    if( n.getKind()==FORALL ){
      ret = getRemoveQuantifiers2( n[1], visited );
    }else if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      bool childrenChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node ni = getRemoveQuantifiers2( n[i], visited );
        childrenChanged = childrenChanged || ni!=n[i];
        children.push_back( ni );
      }
      if( childrenChanged ){
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.insert( children.begin(), n.getOperator() );
        }
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[n] = ret;
    return ret;
  }
}

Node TermDb::getInstConstAttr( Node n ) {
  if (!n.hasAttribute(InstConstantAttribute()) ){
    Node q;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      q = getInstConstAttr(n[i]);
      if( !q.isNull() ){
        break;
      }
    }
    InstConstantAttribute ica;
    n.setAttribute(ica, q);
    if( !q.isNull() ){
      //also set the no-match attribute
      NoMatchAttribute nma;
      n.setAttribute(nma,true);
    }
  }
  return n.getAttribute(InstConstantAttribute());
}

bool TermDb::hasInstConstAttr( Node n ) {
  return !getInstConstAttr(n).isNull();
}

Node TermDb::getBoundVarAttr( Node n ) {
  if (!n.hasAttribute(BoundVarAttribute()) ){
    Node bv;
    if( n.getKind()==BOUND_VARIABLE ){
      bv = n;
    }else{
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bv = getBoundVarAttr(n[i]);
        if( !bv.isNull() ){
          break;
        }
      }
    }
    BoundVarAttribute bva;
    n.setAttribute(bva, bv);
  }
  return n.getAttribute(BoundVarAttribute());
}

bool TermDb::hasBoundVarAttr( Node n ) {
  return !getBoundVarAttr(n).isNull();
}

void TermDb::getBoundVars( Node n, std::vector< Node >& vars ) {
  std::map< Node, bool > visited;
  return getBoundVars2( n, vars, visited );
}

//remove quantifiers
Node TermDb::getRemoveQuantifiers( Node n ) {
  std::map< Node, Node > visited;
  return getRemoveQuantifiers2( n, visited );
}

//quantified simplify 
Node TermDb::getQuantSimplify( Node n ) {
  std::vector< Node > bvs;
  getBoundVars( n, bvs );
  if( bvs.empty() ) {
    return Rewriter::rewrite( n );
  }else{
    Node q = NodeManager::currentNM()->mkNode( FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, bvs ), n );
    q = Rewriter::rewrite( q );
    return getRemoveQuantifiers( q );
  }
}

/** get the i^th instantiation constant of q */
Node TermDb::getInstantiationConstant( Node q, int i ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( q );
  if( it!=d_inst_constants.end() ){
    return it->second[i];
  }else{
    return Node::null();
  }
}

/** get number of instantiation constants for q */
int TermDb::getNumInstantiationConstants( Node q ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( q );
  if( it!=d_inst_constants.end() ){
    return (int)it->second.size();
  }else{
    return 0;
  }
}

Node TermDb::getInstConstantBody( Node q ){
  std::map< Node, Node >::iterator it = d_inst_const_body.find( q );
  if( it==d_inst_const_body.end() ){
    Node n = getInstConstantNode( q[1], q );
    d_inst_const_body[ q ] = n;
    return n;
  }else{
    return it->second;
  }
}

Node TermDb::getCounterexampleLiteral( Node q ){
  if( d_ce_lit.find( q )==d_ce_lit.end() ){
    /*
    Node ceBody = getInstConstantBody( f );
    //check if any variable are of bad types, and fail if so
    for( size_t i=0; i<d_inst_constants[f].size(); i++ ){
      if( d_inst_constants[f][i].getType().isBoolean() ){
        d_ce_lit[ f ] = Node::null();
        return Node::null();
      }
    }
    */
    Node g = NodeManager::currentNM()->mkSkolem( "g", NodeManager::currentNM()->booleanType() );
    //otherwise, ensure literal
    Node ceLit = d_quantEngine->getValuation().ensureLiteral( g );
    d_ce_lit[ q ] = ceLit;
  }
  return d_ce_lit[ q ];
}

Node TermDb::getInstConstantNode( Node n, Node q ){
  makeInstantiationConstantsFor( q );
  Node n2 = n.substitute( d_vars[q].begin(), d_vars[q].end(),
                          d_inst_constants[q].begin(), d_inst_constants[q].end() );
  return n2;
}

Node TermDb::getInstantiatedNode( Node n, Node q, std::vector< Node >& terms ) {
  Assert( d_vars[q].size()==terms.size() );
  return n.substitute( d_vars[q].begin(), d_vars[q].end(), terms.begin(), terms.end() );
}


void getSelfSel( const DatatypeConstructor& dc, Node n, TypeNode ntn, std::vector< Node >& selfSel ){
  for( unsigned j=0; j<dc.getNumArgs(); j++ ){
    TypeNode tn = TypeNode::fromType( ((SelectorType)dc[j].getSelector().getType()).getRangeType() );
    std::vector< Node > ssc;
    if( tn==ntn ){
      ssc.push_back( n );
    }
    /* TODO
    else if( datatypes::DatatypesRewriter::isTypeDatatype( tn ) && std::find( visited.begin(), visited.end(), tn )==visited.end() ){
      visited.push_back( tn );
      const Datatype& dt = ((DatatypeType)(subs[0].getType()).toType()).getDatatype();
      std::vector< Node > disj;
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        getSelfSel( dt[i], n, ntn, ssc );
      }
      visited.pop_back();
    }
    */
    for( unsigned k=0; k<ssc.size(); k++ ){
      selfSel.push_back( NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, dc[j].getSelector(), n ) );
    }
  }
}


Node TermDb::mkSkolemizedBody( Node f, Node n, std::vector< TypeNode >& argTypes, std::vector< TNode >& fvs,
                               std::vector< Node >& sk, Node& sub, std::vector< unsigned >& sub_vars ) {
  Assert( sk.empty() || sk.size()==f[0].getNumChildren() );
  //calculate the variables and substitution
  std::vector< TNode > ind_vars;
  std::vector< unsigned > ind_var_indicies;
  std::vector< TNode > vars;
  std::vector< unsigned > var_indicies;
  for( unsigned i=0; i<f[0].getNumChildren(); i++ ){
    if( isInductionTerm( f[0][i] ) ){
      ind_vars.push_back( f[0][i] );
      ind_var_indicies.push_back( i );
    }else{
      vars.push_back( f[0][i] );
      var_indicies.push_back( i );
    }
    Node s;
    //make the new function symbol or use existing
    if( i>=sk.size() ){
      if( argTypes.empty() ){
        s = NodeManager::currentNM()->mkSkolem( "skv", f[0][i].getType(), "created during skolemization" );
      }else{
        TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, f[0][i].getType() );
        Node op = NodeManager::currentNM()->mkSkolem( "skop", typ, "op created during pre-skolemization" );
        //DOTHIS: set attribute on op, marking that it should not be selected as trigger
        std::vector< Node > funcArgs;
        funcArgs.push_back( op );
        funcArgs.insert( funcArgs.end(), fvs.begin(), fvs.end() );
        s = NodeManager::currentNM()->mkNode( kind::APPLY_UF, funcArgs );
      }
      sk.push_back( s );
    }else{
      Assert( sk[i].getType()==f[0][i].getType() );
    }
  }
  Node ret;
  if( vars.empty() ){
    ret = n;
  }else{
    std::vector< Node > var_sk;
    for( unsigned i=0; i<var_indicies.size(); i++ ){
      var_sk.push_back( sk[var_indicies[i]] );
    }
    Assert( vars.size()==var_sk.size() );
    ret = n.substitute( vars.begin(), vars.end(), var_sk.begin(), var_sk.end() );
  }
  if( !ind_vars.empty() ){
    Trace("sk-ind") << "Ind strengthen : (not " << f << ")" << std::endl;
    Trace("sk-ind") << "Skolemized is : " << ret << std::endl;
    Node n_str_ind;
    TypeNode tn = ind_vars[0].getType();
    Node k = sk[ind_var_indicies[0]];
    Node nret = ret.substitute( ind_vars[0], k );
    //note : everything is under a negation
    //the following constructs ~( R( x, k ) => ~P( x ) )
    if( options::dtStcInduction() && datatypes::DatatypesRewriter::isTypeDatatype(tn) ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      std::vector< Node > disj;
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        std::vector< Node > selfSel;
        getSelfSel( dt[i], k, tn, selfSel );
        std::vector< Node > conj;
        conj.push_back( NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[i].getTester() ), k ).negate() );
        for( unsigned j=0; j<selfSel.size(); j++ ){
          conj.push_back( ret.substitute( ind_vars[0], selfSel[j] ).negate() );
        }
        disj.push_back( conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( OR, conj ) );
      }
      Assert( !disj.empty() );
      n_str_ind = disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( AND, disj );
    }else if( options::intWfInduction() && tn.isInteger() ){
      Node icond = NodeManager::currentNM()->mkNode( GEQ, k, NodeManager::currentNM()->mkConst( Rational(0) ) );
      Node iret = ret.substitute( ind_vars[0], NodeManager::currentNM()->mkNode( MINUS, k, NodeManager::currentNM()->mkConst( Rational(1) ) ) ).negate();
      n_str_ind = NodeManager::currentNM()->mkNode( OR, icond.negate(), iret );
      n_str_ind = NodeManager::currentNM()->mkNode( AND, icond, n_str_ind );
    }else{
      Trace("sk-ind") << "Unknown induction for term : " << ind_vars[0] << ", type = " << tn << std::endl;
      Assert( false );
    }
    Trace("sk-ind") << "Strengthening is : " << n_str_ind << std::endl;

    std::vector< Node > rem_ind_vars;
    rem_ind_vars.insert( rem_ind_vars.end(), ind_vars.begin()+1, ind_vars.end() );
    if( !rem_ind_vars.empty() ){
      Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, rem_ind_vars );
      nret = NodeManager::currentNM()->mkNode( FORALL, bvl, nret );
      nret = Rewriter::rewrite( nret );
      sub = nret;
      sub_vars.insert( sub_vars.end(), ind_var_indicies.begin()+1, ind_var_indicies.end() );
      n_str_ind = NodeManager::currentNM()->mkNode( FORALL, bvl, n_str_ind.negate() ).negate();
    }
    ret = NodeManager::currentNM()->mkNode( OR, nret, n_str_ind );
  }
  Trace("quantifiers-sk") << "mkSkolem body for " << f << " returns : " << ret << std::endl;
  //if it has an instantiation level, set the skolemized body to that level
  if( f.hasAttribute(InstLevelAttribute()) ){
    theory::QuantifiersEngine::setInstantiationLevelAttr( ret, f.getAttribute(InstLevelAttribute()) );
  }
  return ret;
}

Node TermDb::getSkolemizedBody( Node f ){
  Assert( f.getKind()==FORALL );
  if( d_skolem_body.find( f )==d_skolem_body.end() ){
    std::vector< TypeNode > fvTypes;
    std::vector< TNode > fvs;
    Node sub;
    std::vector< unsigned > sub_vars;
    d_skolem_body[ f ] = mkSkolemizedBody( f, f[1], fvTypes, fvs, d_skolem_constants[f], sub, sub_vars );
    //store sub quantifier information
    if( !sub.isNull() ){
      //if we are skolemizing one at a time, we already know the skolem constants of the sub-quantified formula, store them
      Assert( d_skolem_constants[sub].empty() );
      for( unsigned i=0; i<sub_vars.size(); i++ ){
        d_skolem_constants[sub].push_back( d_skolem_constants[f][sub_vars[i]] );
      }
    }
    Assert( d_skolem_constants[f].size()==f[0].getNumChildren() );
    if( options::sortInference() ){
      for( unsigned i=0; i<d_skolem_constants[f].size(); i++ ){
        //carry information for sort inference
        d_quantEngine->getTheoryEngine()->getSortInference()->setSkolemVar( f, f[0][i], d_skolem_constants[f][i] );
      }
    }
  }
  return d_skolem_body[ f ];
}

Node TermDb::getEnumerateTerm( TypeNode tn, unsigned index ) {
  Trace("term-db-enum") << "Get enumerate term " << tn << " " << index << std::endl;
  std::map< TypeNode, unsigned >::iterator it = d_typ_enum_map.find( tn );
  unsigned teIndex;
  if( it==d_typ_enum_map.end() ){
    teIndex = (int)d_typ_enum.size();
    d_typ_enum_map[tn] = teIndex;
    d_typ_enum.push_back( TypeEnumerator(tn) );
  }else{
    teIndex = it->second;
  }
  while( index>=d_enum_terms[tn].size() ){
    if( d_typ_enum[teIndex].isFinished() ){
      return Node::null();
    }
    d_enum_terms[tn].push_back( *d_typ_enum[teIndex] );
    ++d_typ_enum[teIndex];
  }
  return d_enum_terms[tn][index];
}

bool TermDb::isClosedEnumerableType( TypeNode tn ) {
  std::map< TypeNode, bool >::iterator it = d_typ_closed_enum.find( tn );
  if( it==d_typ_closed_enum.end() ){
    bool ret = true;
    if( tn.isArray() || tn.isSort() || tn.isCodatatype() ){
      ret = false;
    }else{
      //TODO: all subfields must be closed enumerable?
    }
    d_typ_closed_enum[tn] = ret;
    return ret;
  }else{
    return it->second;
  }
}

//checks whether a type is not Array and is reasonably small enough (<1000) such that all of its domain elements can be enumerated
bool TermDb::mayComplete( TypeNode tn ) {
  std::map< TypeNode, bool >::iterator it = d_may_complete.find( tn );
  if( it==d_may_complete.end() ){
    bool mc = false;
    if( isClosedEnumerableType( tn ) && tn.getCardinality().isFinite() && !tn.getCardinality().isLargeFinite() ){
      Node card = NodeManager::currentNM()->mkConst( Rational(tn.getCardinality().getFiniteCardinality()) );
      Node oth = NodeManager::currentNM()->mkConst( Rational(1000) );
      Node eq = NodeManager::currentNM()->mkNode( LEQ, card, oth );
      eq = Rewriter::rewrite( eq );
      mc = eq==d_true;
    }
    d_may_complete[tn] = mc;
    return mc;
  }else{
    return it->second;
  }
}

void TermDb::computeVarContains( Node n, std::vector< Node >& varContains ) {
  std::map< Node, bool > visited;
  computeVarContains2( n, varContains, visited );
}

void TermDb::computeVarContains2( Node n, std::vector< Node >& varContains, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==INST_CONSTANT ){
      if( std::find( varContains.begin(), varContains.end(), n )==varContains.end() ){
        varContains.push_back( n );
      }
    }else{
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        computeVarContains2( n[i], varContains, visited );
      }
    }
  }
}

void TermDb::getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains ){
  for( unsigned i=0; i<pats.size(); i++ ){
    varContains[ pats[i] ].clear();
    getVarContainsNode( f, pats[i], varContains[ pats[i] ] );
  }
}

void TermDb::getVarContainsNode( Node f, Node n, std::vector< Node >& varContains ){
  std::vector< Node > vars;
  computeVarContains( n, vars );
  for( unsigned j=0; j<vars.size(); j++ ){
    Node v = vars[j];
    if( v.getAttribute(InstConstantAttribute())==f ){
      if( std::find( varContains.begin(), varContains.end(), v )==varContains.end() ){
        varContains.push_back( v );
      }
    }
  }
}

int TermDb::isInstanceOf2( Node n1, Node n2, std::vector< Node >& varContains1, std::vector< Node >& varContains2 ){
  if( n1==n2 ){
    return 1;
  }else if( n1.getKind()==n2.getKind() ){
    if( n1.getKind()==APPLY_UF ){
      if( n1.getOperator()==n2.getOperator() ){
        int result = 0;
        for( int i=0; i<(int)n1.getNumChildren(); i++ ){
          if( n1[i]!=n2[i] ){
            int cResult = isInstanceOf2( n1[i], n2[i], varContains1, varContains2 );
            if( cResult==0 ){
              return 0;
            }else if( cResult!=result ){
              if( result!=0 ){
                return 0;
              }else{
                result = cResult;
              }
            }
          }
        }
        return result;
      }
    }
    return 0;
  }else if( n2.getKind()==INST_CONSTANT ){
    //if( std::find( d_var_contains[ n1 ].begin(), d_var_contains[ n1 ].end(), n2 )!=d_var_contains[ n1 ].end() ){
    //  return 1;
    //}
    if( varContains1.size()==1 && varContains1[ 0 ]==n2 ){
      return 1;
    }
  }else if( n1.getKind()==INST_CONSTANT ){
    //if( std::find( d_var_contains[ n2 ].begin(), d_var_contains[ n2 ].end(), n1 )!=d_var_contains[ n2 ].end() ){
    //  return -1;
    //}
    if( varContains2.size()==1 && varContains2[ 0 ]==n1 ){
      return 1;
    }
  }
  return 0;
}

int TermDb::isInstanceOf( Node n1, Node n2 ){
  std::vector< Node > varContains1;
  std::vector< Node > varContains2;
  computeVarContains( n1, varContains1 );
  computeVarContains( n1, varContains2 );
  return isInstanceOf2( n1, n2, varContains1, varContains2 );
}

bool TermDb::isUnifiableInstanceOf( Node n1, Node n2, std::map< Node, Node >& subs ){
  if( n1==n2 ){
    return true;
  }else if( n2.getKind()==INST_CONSTANT ){
    //if( !node_contains( n1, n2 ) ){
    //  return false;
    //}
    if( subs.find( n2 )==subs.end() ){
      subs[n2] = n1;
    }else if( subs[n2]!=n1 ){
      return false;
    }
    return true;
  }else if( n1.getKind()==n2.getKind() && n1.getMetaKind()==kind::metakind::PARAMETERIZED ){
    if( n1.getOperator()!=n2.getOperator() ){
      return false;
    }
    for( int i=0; i<(int)n1.getNumChildren(); i++ ){
      if( !isUnifiableInstanceOf( n1[i], n2[i], subs ) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void TermDb::filterInstances( std::vector< Node >& nodes ){
  std::vector< bool > active;
  active.resize( nodes.size(), true );
  std::map< int, std::vector< Node > > varContains;
  for( unsigned i=0; i<nodes.size(); i++ ){
    computeVarContains( nodes[i], varContains[i] );
  }
  for( unsigned i=0; i<nodes.size(); i++ ){
    for( unsigned j=i+1; j<nodes.size(); j++ ){
      if( active[i] && active[j] ){
        int result = isInstanceOf2( nodes[i], nodes[j], varContains[i], varContains[j] );
        if( result==1 ){
          Trace("filter-instances") << nodes[j] << " is an instance of " << nodes[i] << std::endl;
          active[j] = false;
        }else if( result==-1 ){
          Trace("filter-instances") << nodes[i] << " is an instance of " << nodes[j] << std::endl;
          active[i] = false;
        }
      }
    }
  }
  std::vector< Node > temp;
  for( unsigned i=0; i<nodes.size(); i++ ){
    if( active[i] ){
      temp.push_back( nodes[i] );
    }
  }
  nodes.clear();
  nodes.insert( nodes.begin(), temp.begin(), temp.end() );
}

int TermDb::getIdForOperator( Node op ) {
  std::map< Node, int >::iterator it = d_op_id.find( op );
  if( it==d_op_id.end() ){
    d_op_id[op] = d_op_id_count;
    d_op_id_count++;
    return d_op_id[op];
  }else{
    return it->second;
  }
}

int TermDb::getIdForType( TypeNode t ) {
  std::map< TypeNode, int >::iterator it = d_typ_id.find( t );
  if( it==d_typ_id.end() ){
    d_typ_id[t] = d_typ_id_count;
    d_typ_id_count++;
    return d_typ_id[t];
  }else{
    return it->second;
  }
}

bool TermDb::getTermOrder( Node a, Node b ) {
  if( a.getKind()==BOUND_VARIABLE ){
    if( b.getKind()==BOUND_VARIABLE ){
      return a.getAttribute(InstVarNumAttribute())<b.getAttribute(InstVarNumAttribute());
    }else{
      return true;
    }
  }else if( b.getKind()!=BOUND_VARIABLE ){
    Node aop = a.hasOperator() ? a.getOperator() : a;
    Node bop = b.hasOperator() ? b.getOperator() : b;
    Trace("aeq-debug2") << a << "...op..." << aop << std::endl;
    Trace("aeq-debug2") << b << "...op..." << bop << std::endl;
    if( aop==bop ){
      if( a.getNumChildren()==b.getNumChildren() ){
        for( unsigned i=0; i<a.getNumChildren(); i++ ){
          if( a[i]!=b[i] ){
            //first distinct child determines the ordering
            return getTermOrder( a[i], b[i] );
          }
        }
      }else{
        return aop.getNumChildren()<bop.getNumChildren();
      }
    }else{
      return getIdForOperator( aop )<getIdForOperator( bop );
    }
  }
  return false;
}



Node TermDb::getCanonicalFreeVar( TypeNode tn, unsigned i ) {
  Assert( !tn.isNull() );
  while( d_cn_free_var[tn].size()<=i ){
    std::stringstream oss;
    oss << tn;
    std::string typ_name = oss.str();
    while( typ_name[0]=='(' ){
      typ_name.erase( typ_name.begin() );
    }
    std::stringstream os;
    os << typ_name[0] << i;
    Node x = NodeManager::currentNM()->mkBoundVar( os.str().c_str(), tn );
    InstVarNumAttribute ivna;
    x.setAttribute(ivna,d_cn_free_var[tn].size());
    d_cn_free_var[tn].push_back( x );
  }
  return d_cn_free_var[tn][i];
}

struct sortTermOrder {
  TermDb* d_tdb;
  //std::map< Node, std::map< Node, bool > > d_cache;
  bool operator() (Node i, Node j) {
    /*
    //must consult cache since term order is partial?
    std::map< Node, bool >::iterator it = d_cache[j].find( i );
    if( it!=d_cache[j].end() && it->second ){
      return false;
    }else{
      bool ret = d_tdb->getTermOrder( i, j );
      d_cache[i][j] = ret;
      return ret;
    }
    */
    return d_tdb->getTermOrder( i, j );
  }
};

//this function makes a canonical representation of a term (
//  - orders variables left to right
//  - if apply_torder, then sort direct subterms of commutative operators
Node TermDb::getCanonicalTerm( TNode n, std::map< TypeNode, unsigned >& var_count, std::map< TNode, TNode >& subs, bool apply_torder ) {
  Trace("canon-term-debug") << "Get canonical term for " << n << std::endl;
  if( n.getKind()==BOUND_VARIABLE ){
    std::map< TNode, TNode >::iterator it = subs.find( n );
    if( it==subs.end() ){
      TypeNode tn = n.getType();
      //allocate variable
      unsigned vn = var_count[tn];
      var_count[tn]++;
      subs[n] = getCanonicalFreeVar( tn, vn );
      Trace("canon-term-debug") << "...allocate variable." << std::endl;
      return subs[n];
    }else{
      Trace("canon-term-debug") << "...return variable in subs." << std::endl;
      return it->second;
    }
  }else if( n.getNumChildren()>0 ){
    //collect children
    Trace("canon-term-debug") << "Collect children" << std::endl;
    std::vector< Node > cchildren;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      cchildren.push_back( n[i] );
    }
    //if applicable, first sort by term order
    if( apply_torder && isComm( n.getKind() ) ){
      Trace("canon-term-debug") << "Sort based on commutative operator " << n.getKind() << std::endl;
      sortTermOrder sto;
      sto.d_tdb = this;
      std::sort( cchildren.begin(), cchildren.end(), sto );
    }
    //now make canonical
    Trace("canon-term-debug") << "Make canonical children" << std::endl;
    for( unsigned i=0; i<cchildren.size(); i++ ){
      cchildren[i] = getCanonicalTerm( cchildren[i], var_count, subs, apply_torder );
    }
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      Trace("canon-term-debug") << "Insert operator " << n.getOperator() << std::endl;
      cchildren.insert( cchildren.begin(), n.getOperator() );
    }
    Trace("canon-term-debug") << "...constructing for " << n << "." << std::endl;
    Node ret = NodeManager::currentNM()->mkNode( n.getKind(), cchildren );
    Trace("canon-term-debug") << "...constructed " << ret << " for " << n << "." << std::endl;
    return ret;
  }else{
    Trace("canon-term-debug") << "...return 0-child term." << std::endl;
    return n;
  }
}

Node TermDb::getCanonicalTerm( TNode n, bool apply_torder ){
  std::map< TypeNode, unsigned > var_count;
  std::map< TNode, TNode > subs;
  return getCanonicalTerm( n, var_count, subs, apply_torder );
}

void TermDb::getVtsTerms( std::vector< Node >& t, bool isFree, bool create, bool inc_delta ) {
  if( inc_delta ){
    Node delta = getVtsDelta( isFree, create );
    if( !delta.isNull() ){
      t.push_back( delta );
    }
  }
  for( unsigned r=0; r<2; r++ ){
    Node inf = getVtsInfinityIndex( r, isFree, create );
    if( !inf.isNull() ){
      t.push_back( inf );
    }
  }
}

Node TermDb::getVtsDelta( bool isFree, bool create ) {
  if( create ){
    if( d_vts_delta_free.isNull() ){
      d_vts_delta_free = NodeManager::currentNM()->mkSkolem( "delta_free", NodeManager::currentNM()->realType(), "free delta for virtual term substitution" );
      Node delta_lem = NodeManager::currentNM()->mkNode( GT, d_vts_delta_free, d_zero );
      d_quantEngine->getOutputChannel().lemma( delta_lem );
    }
    if( d_vts_delta.isNull() ){
      d_vts_delta = NodeManager::currentNM()->mkSkolem( "delta", NodeManager::currentNM()->realType(), "delta for virtual term substitution" );
    }
  }
  return isFree ? d_vts_delta_free : d_vts_delta;
}

Node TermDb::getVtsInfinity( TypeNode tn, bool isFree, bool create ) {
  if( create ){
    if( d_vts_inf_free[tn].isNull() ){
      d_vts_inf_free[tn] = NodeManager::currentNM()->mkSkolem( "inf_free", tn, "free infinity for virtual term substitution" );
    }
    if( d_vts_inf[tn].isNull() ){
      d_vts_inf[tn] = NodeManager::currentNM()->mkSkolem( "inf", tn, "infinity for virtual term substitution" );
    }
  }
  return isFree ? d_vts_inf_free[tn] : d_vts_inf[tn];
}

Node TermDb::getVtsInfinityIndex( int i, bool isFree, bool create ) {
  if( i==0 ){
    return getVtsInfinity( NodeManager::currentNM()->realType(), isFree, create );
  }else if( i==1 ){
    return getVtsInfinity( NodeManager::currentNM()->integerType(), isFree, create );
  }else{
    Assert( false );
    return Node::null();
  }
}

Node TermDb::substituteVtsFreeTerms( Node n ) {
  std::vector< Node > vars;
  getVtsTerms( vars, false, false );
  std::vector< Node > vars_free;
  getVtsTerms( vars_free, true, false );
  Assert( vars.size()==vars_free.size() );
  if( !vars.empty() ){
    return n.substitute( vars.begin(), vars.end(), vars_free.begin(), vars_free.end() );
  }else{
    return n;
  }
}

Node TermDb::rewriteVtsSymbols( Node n ) {
  if( ( n.getKind()==EQUAL || n.getKind()==GEQ ) ){
    Trace("quant-vts-debug") << "VTS : process " << n << std::endl;
    Node rew_vts_inf;
    bool rew_delta = false;
    //rewriting infinity always takes precedence over rewriting delta
    for( unsigned r=0; r<2; r++ ){
      Node inf = getVtsInfinityIndex( r, false, false );
      if( !inf.isNull() && containsTerm( n, inf ) ){
        if( rew_vts_inf.isNull() ){
          rew_vts_inf = inf;
        }else{
          //for mixed int/real with multiple infinities
          Trace("quant-vts-debug") << "Multiple infinities...equate " << inf << " = " << rew_vts_inf << std::endl;
          std::vector< Node > subs_lhs;
          subs_lhs.push_back( inf );
          std::vector< Node > subs_rhs;
          subs_lhs.push_back( rew_vts_inf );
          n = n.substitute( subs_lhs.begin(), subs_lhs.end(), subs_rhs.begin(), subs_rhs.end() );
          n = Rewriter::rewrite( n );
          //may have cancelled
          if( !containsTerm( n, rew_vts_inf ) ){
            rew_vts_inf = Node::null();
          }
        }
      }
    }
    if( rew_vts_inf.isNull() ){
      if( !d_vts_delta.isNull() && containsTerm( n, d_vts_delta ) ){
        rew_delta = true;
      }
    }
    if( !rew_vts_inf.isNull()  || rew_delta ){
      std::map< Node, Node > msum;
      if( QuantArith::getMonomialSumLit( n, msum ) ){
        if( Trace.isOn("quant-vts-debug") ){
          Trace("quant-vts-debug") << "VTS got monomial sum : " << std::endl;
          QuantArith::debugPrintMonomialSum( msum, "quant-vts-debug" );
        }
        Node vts_sym = !rew_vts_inf.isNull() ? rew_vts_inf : d_vts_delta;
        Assert( !vts_sym.isNull() );
        Node iso_n;
        Node nlit;
        int res = QuantArith::isolate( vts_sym, msum, iso_n, n.getKind(), true );
        if( res!=0 ){
          Trace("quant-vts-debug") << "VTS isolated :  -> " << iso_n << ", res = " << res << std::endl;
          Node slv = iso_n[res==1 ? 1 : 0];
          //ensure the vts terms have been eliminated
          if( containsVtsTerm( slv ) ){
            Trace("quant-vts-warn") << "Bad vts literal : " << n << ", contains " << vts_sym << " but bad solved form " << slv << "." << std::endl;
            nlit = substituteVtsFreeTerms( n );
            Trace("quant-vts-debug") << "...return " << nlit << std::endl;
            //Assert( false );
            //safe case: just convert to free symbols
            return nlit;
          }else{
            if( !rew_vts_inf.isNull() ){
              nlit = ( n.getKind()==GEQ && res==1 ) ? d_true : d_false;
            }else{
              Assert( iso_n[res==1 ? 0 : 1]==d_vts_delta );
              if( n.getKind()==EQUAL ){
                nlit = d_false;
              }else if( res==1 ){
                nlit = NodeManager::currentNM()->mkNode( GEQ, d_zero, slv );
              }else{
                nlit = NodeManager::currentNM()->mkNode( GT, slv, d_zero );
              }
            }
          }
          Trace("quant-vts-debug") << "Return " << nlit << std::endl;
          return nlit;
        }else{
          Trace("quant-vts-warn") << "Bad vts literal : " << n << ", contains " << vts_sym << " but could not isolate." << std::endl;
          //safe case: just convert to free symbols
          nlit = substituteVtsFreeTerms( n );
          Trace("quant-vts-debug") << "...return " << nlit << std::endl;
          //Assert( false );
          return nlit;
        }
      }
    }
    return n;
  }else if( n.getKind()==FORALL ){
    //cannot traverse beneath quantifiers
    return substituteVtsFreeTerms( n );
  }else{
    bool childChanged = false;
    std::vector< Node > children;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Node nn = rewriteVtsSymbols( n[i] );
      children.push_back( nn );
      childChanged = childChanged || nn!=n[i];
    }
    if( childChanged ){
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.insert( children.begin(), n.getOperator() );
      }
      Node ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      Trace("quant-vts-debug") << "...make node " << ret << std::endl;
      return ret;
    }else{
      return n;
    }
  }
}

bool TermDb::containsVtsTerm( Node n, bool isFree ) {
  std::vector< Node > t;
  getVtsTerms( t, isFree, false );
  return containsTerms( n, t );
}

bool TermDb::containsVtsTerm( std::vector< Node >& n, bool isFree ) {
  std::vector< Node > t;
  getVtsTerms( t, isFree, false );
  if( !t.empty() ){
    for( unsigned i=0; i<n.size(); i++ ){
      if( containsTerms( n[i], t ) ){
        return true;
      }
    }
  }
  return false;
}

bool TermDb::containsVtsInfinity( Node n, bool isFree ) {
  std::vector< Node > t;
  getVtsTerms( t, isFree, false, false );
  return containsTerms( n, t );
}

Node TermDb::mkNodeType( Node n, TypeNode tn ) {
  TypeNode ntn = n.getType();
  Assert( ntn.isComparableTo( tn ) );
  if( ntn.isSubtypeOf( tn ) ){
    return n;
  }else{
    if( tn.isInteger() ){
      return NodeManager::currentNM()->mkNode( TO_INTEGER, n );
    }
    return Node::null();
  }
}

bool TermDb::containsTerm2( Node n, Node t, std::map< Node, bool >& visited ) {
  if( n==t ){
    return true;
  }else{
    if( visited.find( n )==visited.end() ){
      visited[n] = true;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsTerm2( n[i], t, visited ) ){
          return true;
        }
      }
    }
    return false;
  }
}

bool TermDb::containsTerms2( Node n, std::vector< Node >& t, std::map< Node, bool >& visited ) {
  if( std::find( t.begin(), t.end(), n )!=t.end() ){
    return true;
  }else{
    if( visited.find( n )==visited.end() ){
      visited[n] = true;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsTerms2( n[i], t, visited ) ){
          return true;
        }
      }
    }
    return false;
  }
}

bool TermDb::containsTerm( Node n, Node t ) {
  std::map< Node, bool > visited;
  return containsTerm2( n, t, visited );
}

bool TermDb::containsTerms( Node n, std::vector< Node >& t ) {
  if( t.empty() ){
    return false;
  }else{
    std::map< Node, bool > visited;
    return containsTerms2( n, t, visited );
  }
}

Node TermDb::simpleNegate( Node n ){
  if( n.getKind()==OR || n.getKind()==AND ){
    std::vector< Node > children;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      children.push_back( simpleNegate( n[i] ) );
    }
    return NodeManager::currentNM()->mkNode( n.getKind()==OR ? AND : OR, children );
  }else{
    return n.negate();
  }
}

bool TermDb::isAssoc( Kind k ) {
  return k==PLUS || k==MULT || k==AND || k==OR || k==XOR || k==IFF ||
         k==BITVECTOR_PLUS || k==BITVECTOR_MULT || k==BITVECTOR_AND || k==BITVECTOR_OR || k==BITVECTOR_XOR || k==BITVECTOR_XNOR || k==BITVECTOR_CONCAT;
}

bool TermDb::isComm( Kind k ) {
  return k==EQUAL || k==PLUS || k==MULT || k==AND || k==OR || k==XOR || k==IFF ||
         k==BITVECTOR_PLUS || k==BITVECTOR_MULT || k==BITVECTOR_AND || k==BITVECTOR_OR || k==BITVECTOR_XOR || k==BITVECTOR_XNOR;
}

bool TermDb::isBoolConnective( Kind k ) {
  return k==OR || k==AND || k==IFF || k==ITE || k==FORALL || k==NOT;
}

void TermDb::registerTrigger( theory::inst::Trigger* tr, Node op ){
  if( std::find( d_op_triggers[op].begin(), d_op_triggers[op].end(), tr )==d_op_triggers[op].end() ){
    d_op_triggers[op].push_back( tr );
  }
}

bool TermDb::isInductionTerm( Node n ) {
  if( options::dtStcInduction() && datatypes::DatatypesRewriter::isTermDatatype( n ) ){
    const Datatype& dt = ((DatatypeType)(n.getType()).toType()).getDatatype();
    return !dt.isCodatatype();
  }
  if( options::intWfInduction() && n.getType().isInteger() ){
    return true;
  }
  return false;
}

bool TermDb::isRewriteRule( Node q ) {
  return !getRewriteRule( q ).isNull();
}

Node TermDb::getRewriteRule( Node q ) {
  if( q.getKind()==FORALL && q.getNumChildren()==3 && q[2].getNumChildren()>0 && q[2][0][0].getKind()==REWRITE_RULE ){
    return q[2][0][0];
  }else{
    return Node::null();
  }
}

bool TermDb::isFunDef( Node q ) {
  return !getFunDefHead( q ).isNull();
}

bool TermDb::isFunDefAnnotation( Node ipl ) {
  if( !ipl.isNull() ){
    for( unsigned i=0; i<ipl.getNumChildren(); i++ ){
      if( ipl[i].getKind()==INST_ATTRIBUTE ){
        if( ipl[i][0].getAttribute(FunDefAttribute()) ){
          return true;
        }
      }
    }
  }
  return false;
}

Node TermDb::getFunDefHead( Node q ) {
  //&& ( q[1].getKind()==EQUAL || q[1].getKind()==IFF ) && q[1][0].getKind()==APPLY_UF &&
  if( q.getKind()==FORALL && q.getNumChildren()==3 ){

    for( unsigned i=0; i<q[2].getNumChildren(); i++ ){
      if( q[2][i].getKind()==INST_ATTRIBUTE ){
        if( q[2][i][0].getAttribute(FunDefAttribute()) ){
          return q[2][i][0];
        }
      }
    }
  }
  return Node::null();
}
Node TermDb::getFunDefBody( Node q ) {
  Node h = getFunDefHead( q );
  if( !h.isNull() ){
    if( q[1].getKind()==EQUAL || q[1].getKind()==IFF ){
      if( q[1][0]==h ){
        return q[1][1];
      }else if( q[1][1]==h ){
        return q[1][0];
      }
    }else{
      Node atom = q[1].getKind()==NOT ? q[1][0] : q[1];
      bool pol = q[1].getKind()!=NOT;
      if( atom==h ){
        return NodeManager::currentNM()->mkConst( pol );
      }
    }
  }
  return Node::null();
}

bool TermDb::isSygusConjecture( Node q ) {
  return ( q.getKind()==FORALL && q.getNumChildren()==3 ) ? isSygusConjectureAnnotation( q[2] ) : false;
}

bool TermDb::isSygusConjectureAnnotation( Node ipl ){
  if( !ipl.isNull() ){
    for( unsigned i=0; i<ipl.getNumChildren(); i++ ){
      if( ipl[i].getKind()==INST_ATTRIBUTE ){
        Node avar = ipl[i][0];
        if( avar.getAttribute(SygusAttribute()) ){
          return true;
        }
      }
    }
  }
  return false;
}

void TermDb::computeAttributes( Node q ) {
  Trace("quant-attr-debug") << "Compute attributes for " << q << std::endl;
  if( q.getNumChildren()==3 ){
    for( unsigned i=0; i<q[2].getNumChildren(); i++ ){
      Trace("quant-attr-debug") << "Check : " << q[2][i] << " " << q[2][i].getKind() << std::endl;
      if( q[2][i].getKind()==INST_ATTRIBUTE ){
        Node avar = q[2][i][0];
        if( avar.getAttribute(AxiomAttribute()) ){
          Trace("quant-attr") << "Attribute : axiom : " << q << std::endl;
          d_qattr_axiom[q] = true;
        }
        if( avar.getAttribute(ConjectureAttribute()) ){
          Trace("quant-attr") << "Attribute : conjecture : " << q << std::endl;
          d_qattr_conjecture[q] = true;
        }
        if( avar.getAttribute(FunDefAttribute()) ){
          Trace("quant-attr") << "Attribute : function definition : " << q << std::endl;
          d_qattr_fundef[q] = true;
          //get operator directly from pattern
          Node f = q[2][i][0].getOperator();
          if( d_fun_defs.find( f )!=d_fun_defs.end() ){
            Message() << "Cannot define function " << f << " more than once." << std::endl;
            exit( 0 );
          }
          d_fun_defs[f] = true;
          d_quantEngine->setOwner( q, d_quantEngine->getFunDefEngine() );
        }
        if( avar.getAttribute(SygusAttribute()) ){
          //not necessarily nested existential
          //Assert( q[1].getKind()==NOT );
          //Assert( q[1][0].getKind()==FORALL );

          Trace("quant-attr") << "Attribute : sygus : " << q << std::endl;
          d_qattr_sygus[q] = true;
          if( d_quantEngine->getCegInstantiation()==NULL ){
            Trace("quant-warn") << "WARNING : ceg instantiation is null, and we have : " << q << std::endl;
          }
          d_quantEngine->setOwner( q, d_quantEngine->getCegInstantiation() );
        }
        if( avar.getAttribute(SynthesisAttribute()) ){
          Trace("quant-attr") << "Attribute : synthesis : " << q << std::endl;
          d_qattr_synthesis[q] = true;
          if( d_quantEngine->getCegInstantiation()==NULL ){
            Trace("quant-warn") << "WARNING : ceg instantiation is null, and we have : " << q << std::endl;
          }
          d_quantEngine->setOwner( q, d_quantEngine->getCegInstantiation() );
        }
        if( avar.hasAttribute(QuantInstLevelAttribute()) ){
          d_qattr_qinstLevel[q] = avar.getAttribute(QuantInstLevelAttribute());
          Trace("quant-attr") << "Attribute : quant inst level " << d_qattr_qinstLevel[q] << " : " << q << std::endl;
        }
        if( avar.hasAttribute(RrPriorityAttribute()) ){
          d_qattr_rr_priority[q] = avar.getAttribute(RrPriorityAttribute());
          Trace("quant-attr") << "Attribute : rr priority " << d_qattr_rr_priority[q] << " : " << q << std::endl;
        }
        if( avar.getKind()==REWRITE_RULE ){
          Trace("quant-attr") << "Attribute : rewrite rule : " << q << std::endl;
          Assert( i==0 );
          if( d_quantEngine->getRewriteEngine()==NULL ){
            Trace("quant-warn") << "WARNING : rewrite engine is null, and we have : " << q << std::endl;
          }
          //set rewrite engine as owner
          d_quantEngine->setOwner( q, d_quantEngine->getRewriteEngine() );
        }
      }
    }
  }
}

bool TermDb::isQAttrConjecture( Node q ) {
  std::map< Node, bool >::iterator it = d_qattr_conjecture.find( q );
  if( it==d_qattr_conjecture.end() ){
    return false;
  }else{
    return it->second;
  }
}

bool TermDb::isQAttrAxiom( Node q ) {
  std::map< Node, bool >::iterator it = d_qattr_axiom.find( q );
  if( it==d_qattr_axiom.end() ){
    return false;
  }else{
    return it->second;
  }
}

bool TermDb::isQAttrFunDef( Node q ) {
  std::map< Node, bool >::iterator it = d_qattr_fundef.find( q );
  if( it==d_qattr_fundef.end() ){
    return false;
  }else{
    return it->second;
  }
}

bool TermDb::isQAttrSygus( Node q ) {
  std::map< Node, bool >::iterator it = d_qattr_sygus.find( q );
  if( it==d_qattr_sygus.end() ){
    return false;
  }else{
    return it->second;
  }
}

bool TermDb::isQAttrSynthesis( Node q ) {
  std::map< Node, bool >::iterator it = d_qattr_synthesis.find( q );
  if( it==d_qattr_synthesis.end() ){
    return false;
  }else{
    return it->second;
  }
}

int TermDb::getQAttrQuantInstLevel( Node q ) {
  std::map< Node, int >::iterator it = d_qattr_qinstLevel.find( q );
  if( it==d_qattr_qinstLevel.end() ){
    return -1;
  }else{
    return it->second;
  }
}

int TermDb::getQAttrRewriteRulePriority( Node q ) {
  std::map< Node, int >::iterator it = d_qattr_rr_priority.find( q );
  if( it==d_qattr_rr_priority.end() ){
    return -1;
  }else{
    return it->second;
  }
}



TermDbSygus::TermDbSygus(){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

TNode TermDbSygus::getVar( TypeNode tn, int i ) {
  while( i>=(int)d_fv[tn].size() ){
    std::stringstream ss;
    TypeNode vtn = tn;
    if( datatypes::DatatypesRewriter::isTypeDatatype( tn ) ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      ss << "fv_" << dt.getName() << "_" << i;
      if( !dt.getSygusType().isNull() ){
        vtn = TypeNode::fromType( dt.getSygusType() );
      }
    }else{
      ss << "fv_" << tn << "_" << i;
    }
    Assert( !vtn.isNull() );
    Node v = NodeManager::currentNM()->mkSkolem( ss.str(), vtn, "for sygus normal form testing" );
    d_fv_stype[v] = tn;
    d_fv_num[v] = i;
    d_fv[tn].push_back( v );
  }
  return d_fv[tn][i];
}

TNode TermDbSygus::getVarInc( TypeNode tn, std::map< TypeNode, int >& var_count ) {
  std::map< TypeNode, int >::iterator it = var_count.find( tn );
  if( it==var_count.end() ){
    var_count[tn] = 1;
    return getVar( tn, 0 );
  }else{
    int index = it->second;
    var_count[tn]++;
    return getVar( tn, index );
  }
}

TypeNode TermDbSygus::getSygusTypeForVar( Node v ) {
  Assert( d_fv_stype.find( v )!=d_fv_stype.end() );
  return d_fv_stype[v];
}

bool TermDbSygus::getMatch( Node p, Node n, std::map< int, Node >& s ) {
  std::vector< int > new_s;
  return getMatch2( p, n, s, new_s );
}

bool TermDbSygus::getMatch2( Node p, Node n, std::map< int, Node >& s, std::vector< int >& new_s ) {
  std::map< Node, int >::iterator it = d_fv_num.find( p );
  if( it!=d_fv_num.end() ){
    Node prev = s[it->second];
    s[it->second] = n;
    if( prev.isNull() ){
      new_s.push_back( it->second );
    }
    return prev.isNull() || prev==n;
  }else if( n.getNumChildren()==0 ){
    return p==n;
  }else if( n.getKind()==p.getKind() && n.getNumChildren()==p.getNumChildren() ){
    //try both ways?
    unsigned rmax = TermDb::isComm( n.getKind() ) && n.getNumChildren()==2 ? 2 : 1;
    std::vector< int > new_tmp;
    for( unsigned r=0; r<rmax; r++ ){
      bool success = true;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        int io = r==0 ? i : ( i==0 ? 1 : 0 );
        if( !getMatch2( p[i], n[io], s, new_tmp ) ){
          success = false;
          for( unsigned j=0; j<new_tmp.size(); j++ ){
            s.erase( new_tmp[j] );
          }
          new_tmp.clear();
          break;
        }
      }
      if( success ){
        new_s.insert( new_s.end(), new_tmp.begin(), new_tmp.end() );
        return true;
      }
    }
  }
  return false;
}

bool TermDbSygus::getMatch( Node t, TypeNode st, int& index_found, std::vector< Node >& args, int index_exc, int index_start ) {
  Assert( datatypes::DatatypesRewriter::isTypeDatatype( st ) );
  const Datatype& dt = ((DatatypeType)(st).toType()).getDatatype();
  Assert( dt.isSygus() );
  std::map< Kind, std::vector< Node > > kgens;
  std::vector< Node > gens;
  for( unsigned i=index_start; i<dt.getNumConstructors(); i++ ){
    if( (int)i!=index_exc ){
      Node g = getGenericBase( st, dt, i );
      gens.push_back( g );
      kgens[g.getKind()].push_back( g );
      Trace("sygus-db-debug") << "Check generic base : " << g << " from " << dt[i].getName() << std::endl;
      if( g.getKind()==t.getKind() ){
        Trace("sygus-db-debug") << "Possible match ? " << g << " " << t << " for " << dt[i].getName() << std::endl;
        std::map< int, Node > sigma;
        if( getMatch( g, t, sigma ) ){
          //we found an exact match
          bool msuccess = true;
          for( unsigned j=0; j<dt[i].getNumArgs(); j++ ){
            if( sigma[j].isNull() ){
              msuccess = false;
              break;
            }else{
              args.push_back( sigma[j] );
            }
          }
          if( msuccess ){
            index_found = i;
            return true;
          }
          //we found an exact match
          //std::map< TypeNode, int > var_count;
          //Node new_t = mkGeneric( dt, i, var_count, args );
          //Trace("sygus-db-debug") << "Rewrote to : " << new_t << std::endl;
          //return new_t;
        }
      }
    }
  }
  /*
  //otherwise, try to modulate based on kinds
  for( std::map< Kind, std::vector< Node > >::iterator it = kgens.begin(); it != kgens.end(); ++it ){
    if( it->second.size()>1 ){
      for( unsigned i=0; i<it->second.size(); i++ ){
        for( unsigned j=0; j<it->second.size(); j++ ){
          if( i!=j ){
            std::map< int, Node > sigma;
            if( getMatch( it->second[i], it->second[j], sigma ) ){
              if( sigma.size()==1 ){
                //Node mod_pat = sigma.begin().second;
                //Trace("cegqi-si-rcons-debug") << "Modulated pattern " << mod_pat << " from " << it->second[i] << " and " << it->second[j] << std::endl;
              }
            }
          }
        }
      }
    }
  }
  */
  return false;
}

Node TermDbSygus::getGenericBase( TypeNode tn, const Datatype& dt, int c ) {
  std::map< int, Node >::iterator it = d_generic_base[tn].find( c );
  if( it==d_generic_base[tn].end() ){
    registerSygusType( tn );
    std::map< TypeNode, int > var_count;
    std::map< int, Node > pre;
    Node g = mkGeneric( dt, c, var_count, pre );
    Trace("sygus-db-debug") << "Sygus DB : Generic is " << g << std::endl;
    Node gr = Rewriter::rewrite( g );
    Trace("sygus-db-debug") << "Sygus DB : Generic rewritten is " << gr << std::endl;
    gr = Node::fromExpr( smt::currentSmtEngine()->expandDefinitions( gr.toExpr() ) );
    Trace("sygus-db") << "Sygus DB : Generic base " << dt[c].getName() << " : " << gr << std::endl;
    d_generic_base[tn][c] = gr;
    return gr;
  }else{
    return it->second;
  }
}

Node TermDbSygus::mkGeneric( const Datatype& dt, int c, std::map< TypeNode, int >& var_count, std::map< int, Node >& pre ) {
  Assert( c>=0 && c<(int)dt.getNumConstructors() );
  Assert( dt.isSygus() );
  Assert( !dt[c].getSygusOp().isNull() );
  std::vector< Node > children;
  Node op = Node::fromExpr( dt[c].getSygusOp() );
  if( op.getKind()!=BUILTIN ){
    children.push_back( op );
  }
  Trace("sygus-db") << "mkGeneric " << dt.getName() << " " << op << " " << op.getKind() << "..." << std::endl;
  for( int i=0; i<(int)dt[c].getNumArgs(); i++ ){
    TypeNode tna = getArgType( dt[c], i );
    Node a;
    std::map< int, Node >::iterator it = pre.find( i );
    if( it!=pre.end() ){
      a = it->second;
    }else{
      a = getVarInc( tna, var_count );
    }
    Assert( !a.isNull() );
    children.push_back( a );
  }
  Node ret;
  if( op.getKind()==BUILTIN ){
    ret = NodeManager::currentNM()->mkNode( op, children );
  }else{
    Kind ok = getOperatorKind( op );
    Trace("sygus-db") << "Operator kind is " << ok << std::endl;
    if( children.size()==1 && ok==kind::UNDEFINED_KIND ){
      ret = children[0];
    }else{
      ret = NodeManager::currentNM()->mkNode( ok, children );
      /*
      Node n = NodeManager::currentNM()->mkNode( APPLY, children );
      //must expand definitions
      Node ne = Node::fromExpr( smt::currentSmtEngine()->expandDefinitions( n.toExpr() ) );
      Trace("sygus-db-debug") << "Expanded definitions in " << n << " to " << ne << std::endl;
      return ne;
      */
    }
  }
  Trace("sygus-db") << "...returning " << ret << std::endl;
  return ret;
}

Node TermDbSygus::sygusToBuiltin( Node n, TypeNode tn ) {
  std::map< Node, Node >::iterator it = d_sygus_to_builtin[tn].find( n );
  if( it==d_sygus_to_builtin[tn].end() ){
    Trace("sygus-db-debug") << "SygusToBuiltin : compute for " << n << ", type = " << tn << std::endl;
    Assert( n.getKind()==APPLY_CONSTRUCTOR );
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    unsigned i = Datatype::indexOf( n.getOperator().toExpr() );
    Assert( n.getNumChildren()==dt[i].getNumArgs() );
    std::map< TypeNode, int > var_count;
    std::map< int, Node > pre;
    for( unsigned j=0; j<n.getNumChildren(); j++ ){
      pre[j] = sygusToBuiltin( n[j], getArgType( dt[i], j ) );
    }
    Node ret = mkGeneric( dt, i, var_count, pre );
    Trace("sygus-db-debug") << "SygusToBuiltin : Generic is " << ret << std::endl;
    ret = Node::fromExpr( smt::currentSmtEngine()->expandDefinitions( ret.toExpr() ) );
    Trace("sygus-db-debug") << "SygusToBuiltin : After expand definitions " << ret << std::endl;
    d_sygus_to_builtin[tn][n] = ret;
    return ret;
  }else{
    return it->second;
  }
}

//rcons_depth limits the number of recursive calls when doing accelerated constant reconstruction (currently limited to 1000)
//this is hacky : depending upon order of calls, constant rcons may succeed, e.g. 1001, 999 vs. 999, 1001
Node TermDbSygus::builtinToSygusConst( Node c, TypeNode tn, int rcons_depth ) {
  std::map< Node, Node >::iterator it = d_builtin_const_to_sygus[tn].find( c );
  if( it==d_builtin_const_to_sygus[tn].end() ){
    Node sc;
    d_builtin_const_to_sygus[tn][c] = sc;
    Assert( c.isConst() );
    Assert( datatypes::DatatypesRewriter::isTypeDatatype( tn ) );
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    Trace("csi-rcons-debug") << "Try to reconstruct " << c << " in " << dt.getName() << std::endl;
    Assert( dt.isSygus() );
    // if we are not interested in reconstructing constants, or the grammar allows them, return a proxy
    if( !options::cegqiSingleInvReconstructConst() || dt.getSygusAllowConst() ){
      Node k = NodeManager::currentNM()->mkSkolem( "sy", tn, "sygus proxy" );
      SygusProxyAttribute spa;
      k.setAttribute(spa,c);
      sc = k;
    }else{
      int carg = getOpArg( tn, c );
      if( carg!=-1 ){
        //sc = Node::fromExpr( dt[carg].getSygusOp() );
        sc = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, Node::fromExpr( dt[carg].getConstructor() ) );
      }else{
        //identity functions
        for( unsigned i=0; i<getNumIdFuncs( tn ); i++ ){
          unsigned ii = getIdFuncIndex( tn, i );
          Assert( dt[ii].getNumArgs()==1 );
          //try to directly reconstruct from single argument
          TypeNode tnc = getArgType( dt[ii], 0 );
          Trace("csi-rcons-debug") << "Based on id function " << dt[ii].getSygusOp() << ", try reconstructing " << c << " instead in " << tnc << std::endl;
          Node n = builtinToSygusConst( c, tnc, rcons_depth );
          if( !n.isNull() ){
            sc = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, Node::fromExpr( dt[ii].getConstructor() ), n );
            break;
          }
        }
        if( sc.isNull() ){
          if( rcons_depth<1000 ){
            //accelerated, recursive reconstruction of constants
            Kind pk = getPlusKind( TypeNode::fromType( dt.getSygusType() ) );
            if( pk!=UNDEFINED_KIND ){
              int arg = getKindArg( tn, pk );
              if( arg!=-1 ){
                Kind ck = getComparisonKind( TypeNode::fromType( dt.getSygusType() ) );
                Kind pkm = getPlusKind( TypeNode::fromType( dt.getSygusType() ), true );
                //get types
                Assert( dt[arg].getNumArgs()==2 );
                TypeNode tn1 = getArgType( dt[arg], 0 );
                TypeNode tn2 = getArgType( dt[arg], 1 );
                //iterate over all positive constants, largest to smallest
                int start = d_const_list[tn1].size()-1;
                int end = d_const_list[tn1].size()-d_const_list_pos[tn1];
                for( int i=start; i>=end; --i ){
                  Node c1 = d_const_list[tn1][i];
                  //only consider if smaller than c, and
                  if( doCompare( c1, c, ck ) ){
                    Node c2 = NodeManager::currentNM()->mkNode( pkm, c, c1 );
                    c2 = Rewriter::rewrite( c2 );
                    if( c2.isConst() ){
                      //reconstruct constant on the other side
                      Node sc2 = builtinToSygusConst( c2, tn2, rcons_depth+1 );
                      if( !sc2.isNull() ){
                        Node sc1 = builtinToSygusConst( c1, tn1, rcons_depth );
                        Assert( !sc1.isNull() );
                        sc = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, Node::fromExpr( dt[arg].getConstructor() ), sc1, sc2 );
                        break;
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    d_builtin_const_to_sygus[tn][c] = sc;
    return sc;
  }else{
    return it->second;
  }
}

Node TermDbSygus::getSygusNormalized( Node n, std::map< TypeNode, int >& var_count, std::map< Node, Node >& subs ) {
  return n;
  /*  TODO?
  if( n.getKind()==SKOLEM ){
    std::map< Node, Node >::iterator its = subs.find( n );
    if( its!=subs.end() ){
      return its->second;
    }else{
      std::map< Node, TypeNode >::iterator it = d_fv_stype.find( n );
      if( it!=d_fv_stype.end() ){
        Node v = getVarInc( it->second, var_count );
        subs[n] = v;
        return v;
      }else{
        return n;
      }
    }
  }else{
    if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = getSygusNormalized( n[i], var_count, subs );
        childChanged = childChanged || nc!=n[i];
        children.push_back( nc );
      }
      if( childChanged ){
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    return n;
  }
  */
}

Node TermDbSygus::getNormalized( TypeNode t, Node prog, bool do_pre_norm, bool do_post_norm ) {
  if( do_pre_norm ){
    std::map< TypeNode, int > var_count;
    std::map< Node, Node > subs;
    prog = getSygusNormalized( prog, var_count, subs );
  }
  std::map< Node, Node >::iterator itn = d_normalized[t].find( prog );
  if( itn==d_normalized[t].end() ){
    Node progr = Node::fromExpr( smt::currentSmtEngine()->expandDefinitions( prog.toExpr() ) );
    progr = Rewriter::rewrite( progr );
    if( do_post_norm ){
      std::map< TypeNode, int > var_count;
      std::map< Node, Node > subs;
      progr = getSygusNormalized( progr, var_count, subs );
    }
    Trace("sygus-sym-break2") << "...rewrites to " << progr << std::endl;
    d_normalized[t][prog] = progr;
    return progr;
  }else{
    return itn->second;
  }
}

int TermDbSygus::getSygusTermSize( Node n ){
  if( isVar( n ) ){
    return 0;
  }else{
    int sum = 0;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      sum += getSygusTermSize( n[i] );
    }
    return 1+sum;
  }
}

bool TermDbSygus::isAntisymmetric( Kind k, Kind& dk ) {
  if( k==GT ){
    dk = LT;
    return true;
  }else if( k==GEQ ){
    dk = LEQ;
    return true;
  }else if( k==BITVECTOR_UGT ){
    dk = BITVECTOR_ULT;
    return true;
  }else if( k==BITVECTOR_UGE ){
    dk = BITVECTOR_ULE;
    return true;
  }else if( k==BITVECTOR_SGT ){
    dk = BITVECTOR_SLT;
    return true;
  }else if( k==BITVECTOR_SGE ){
    dk = BITVECTOR_SLE;
    return true;
  }else{
    return false;
  }
}

bool TermDbSygus::isIdempotentArg( Node n, Kind ik, int arg ) {
  TypeNode tn = n.getType();
  if( n==getTypeValue( tn, 0 ) ){
    if( ik==PLUS || ik==OR || ik==XOR || ik==BITVECTOR_PLUS || ik==BITVECTOR_OR || ik==BITVECTOR_XOR ){
      return true;
    }else if( ik==MINUS || ik==BITVECTOR_SHL || ik==BITVECTOR_LSHR || ik==BITVECTOR_SUB ){
      return arg==1;
    }
  }else if( n==getTypeValue( tn, 1 ) ){
    if( ik==MULT || ik==BITVECTOR_MULT ){
      return true;
    }else if( ik==DIVISION || ik==BITVECTOR_UDIV || ik==BITVECTOR_SDIV ){
      return arg==1;
    }
  }else if( n==getTypeMaxValue( tn ) ){
    if( ik==IFF || ik==BITVECTOR_AND || ik==BITVECTOR_XNOR ){
      return true;
    }
  }
  return false;
}


bool TermDbSygus::isSingularArg( Node n, Kind ik, int arg ) {
  TypeNode tn = n.getType();
  if( n==getTypeValue( tn, 0 ) ){
    if( ik==AND || ik==MULT || ik==BITVECTOR_AND || ik==BITVECTOR_MULT ){
      return true;
    }else if( ik==DIVISION || ik==BITVECTOR_UDIV || ik==BITVECTOR_SDIV ){
      return arg==0;
    }
  }else if( n==getTypeMaxValue( tn ) ){
    if( ik==OR || ik==BITVECTOR_OR ){
      return true;
    }
  }
  return false;
}

bool TermDbSygus::hasOffsetArg( Kind ik, int arg, int& offset, Kind& ok ) {
  if( ik==LT ){
    Assert( arg==0 || arg==1 );
    offset = arg==0 ? 1 : -1;
    ok = LEQ;
    return true;
  }else if( ik==BITVECTOR_ULT ){
    Assert( arg==0 || arg==1 );
    offset = arg==0 ? 1 : -1;
    ok = BITVECTOR_ULE;
    return true;
  }else if( ik==BITVECTOR_SLT ){
    Assert( arg==0 || arg==1 );
    offset = arg==0 ? 1 : -1;
    ok = BITVECTOR_SLE;
    return true;
  }
  return false;
}


Node TermDbSygus::getTypeValue( TypeNode tn, int val ) {
  std::map< int, Node >::iterator it = d_type_value[tn].find( val );
  if( it==d_type_value[tn].end() ){
    Node n;
    if( tn.isInteger() || tn.isReal() ){
      Rational c(val);
      n = NodeManager::currentNM()->mkConst( c );
    }else if( tn.isBitVector() ){
      unsigned int uv = val;
      BitVector bval(tn.getConst<BitVectorSize>(), uv);
      n = NodeManager::currentNM()->mkConst<BitVector>(bval);
    }else if( tn.isBoolean() ){
      if( val==0 ){
        n = d_false;
      }
    }
    d_type_value[tn][val] = n;
    return n;
  }else{
    return it->second;
  }
}

Node TermDbSygus::getTypeMaxValue( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_type_max_value.find( tn );
  if( it==d_type_max_value.end() ){
    Node n;
    if( tn.isBitVector() ){
      n = bv::utils::mkOnes(tn.getConst<BitVectorSize>());
    }else if( tn.isBoolean() ){
      n = d_true;
    }
    d_type_max_value[tn] = n;
    return n;
  }else{
    return it->second;
  }
}

Node TermDbSygus::getTypeValueOffset( TypeNode tn, Node val, int offset, int& status ) {
  std::map< int, Node >::iterator it = d_type_value_offset[tn][val].find( offset );
  if( it==d_type_value_offset[tn][val].end() ){
    Node val_o;
    Node offset_val = getTypeValue( tn, offset );
    status = -1;
    if( !offset_val.isNull() ){
      if( tn.isInteger() || tn.isReal() ){
        val_o = Rewriter::rewrite( NodeManager::currentNM()->mkNode( PLUS, val, offset_val ) );
        status = 0;
      }else if( tn.isBitVector() ){
        val_o = Rewriter::rewrite( NodeManager::currentNM()->mkNode( BITVECTOR_PLUS, val, offset_val ) );
      }
    }
    d_type_value_offset[tn][val][offset] = val_o;
    d_type_value_offset_status[tn][val][offset] = status;
    return val_o;
  }else{
    status = d_type_value_offset_status[tn][val][offset];
    return it->second;
  }
}

struct sortConstants {
  TermDbSygus * d_tds;
  Kind d_comp_kind;
  bool operator() (Node i, Node j) {
    if( i!=j ){
      return d_tds->doCompare( i, j, d_comp_kind );
    }else{
      return false;
    }
  }
};

void TermDbSygus::registerSygusType( TypeNode tn ){
  if( d_register.find( tn )==d_register.end() ){
    if( !datatypes::DatatypesRewriter::isTypeDatatype( tn ) ){
      d_register[tn] = TypeNode::null();
    }else{
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      Trace("sygus-db") << "Register type " << dt.getName() << "..." << std::endl;
      d_register[tn] = TypeNode::fromType( dt.getSygusType() );
      if( d_register[tn].isNull() ){
        Trace("sygus-db") << "...not sygus." << std::endl;
      }else{
        //for constant reconstruction
        Kind ck = getComparisonKind( TypeNode::fromType( dt.getSygusType() ) );
        Node z = getTypeValue( TypeNode::fromType( dt.getSygusType() ), 0 );
        d_const_list_pos[tn] = 0;
        //iterate over constructors
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          Expr sop = dt[i].getSygusOp();
          Assert( !sop.isNull() );
          Node n = Node::fromExpr( sop );
          Trace("sygus-db") << "  Operator #" << i << " : " << sop;
          if( sop.getKind() == kind::BUILTIN ){
            Kind sk = NodeManager::operatorToKind( n );
            Trace("sygus-db") << ", kind = " << sk;
            d_kinds[tn][sk] = i;
            d_arg_kind[tn][i] = sk;
          }else if( sop.isConst() ){
            Trace("sygus-db") << ", constant";
            d_consts[tn][n] = i;
            d_arg_const[tn][i] = n;
            d_const_list[tn].push_back( n );
            if( ck!=UNDEFINED_KIND && doCompare( z, n, ck ) ){
              d_const_list_pos[tn]++;
            }
          }
          if( dt[i].isSygusIdFunc() ){
            d_id_funcs[tn].push_back( i );
          }
          d_ops[tn][n] = i;
          d_arg_ops[tn][i] = n;
          Trace("sygus-db") << std::endl;
        }
        //sort the constant list
        if( !d_const_list[tn].empty() ){
          if( ck!=UNDEFINED_KIND ){
            sortConstants sc;
            sc.d_comp_kind = ck;
            sc.d_tds = this;
            std::sort( d_const_list[tn].begin(), d_const_list[tn].end(), sc );
          }
          Trace("sygus-db") << "Type has " << d_const_list[tn].size() << " constants..." << std::endl << "  ";
          for( unsigned i=0; i<d_const_list[tn].size(); i++ ){
            Trace("sygus-db") << d_const_list[tn][i] << " ";
          }
          Trace("sygus-db") << std::endl;
          Trace("sygus-db") << "Of these, " << d_const_list_pos[tn] << " are marked as positive." << std::endl;
        }
        //register connected types
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          for( unsigned j=0; j<dt[i].getNumArgs(); j++ ){
            registerSygusType( getArgType( dt[i], j ) );
          }
        }
      }
    }
  }
}

bool TermDbSygus::isRegistered( TypeNode tn ) {
  return d_register.find( tn )!=d_register.end();
}

TypeNode TermDbSygus::sygusToBuiltinType( TypeNode tn ) {
  Assert( isRegistered( tn ) );
  return d_register[tn];
}

int TermDbSygus::getKindArg( TypeNode tn, Kind k ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< Kind, int > >::iterator itt = d_kinds.find( tn );
  if( itt!=d_kinds.end() ){
    std::map< Kind, int >::iterator it = itt->second.find( k );
    if( it!=itt->second.end() ){
      return it->second;
    }
  }
  return -1;
}

int TermDbSygus::getConstArg( TypeNode tn, Node n ){
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< Node, int > >::iterator itt = d_consts.find( tn );
  if( itt!=d_consts.end() ){
    std::map< Node, int >::iterator it = itt->second.find( n );
    if( it!=itt->second.end() ){
      return it->second;
    }
  }
  return -1;
}

int TermDbSygus::getOpArg( TypeNode tn, Node n ) {
  std::map< Node, int >::iterator it = d_ops[tn].find( n );
  if( it!=d_ops[tn].end() ){
    return it->second;
  }else{
    return -1;
  }
}

bool TermDbSygus::hasKind( TypeNode tn, Kind k ) {
  return getKindArg( tn, k )!=-1;
}
bool TermDbSygus::hasConst( TypeNode tn, Node n ) {
  return getConstArg( tn, n )!=-1;
}
bool TermDbSygus::hasOp( TypeNode tn, Node n ) {
  return getOpArg( tn, n )!=-1;
}

Node TermDbSygus::getArgOp( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Node > >::iterator itt = d_arg_ops.find( tn );
  if( itt!=d_arg_ops.end() ){
    std::map< int, Node >::iterator itn = itt->second.find( i );
    if( itn!=itt->second.end() ){
      return itn->second;
    }
  }
  return Node::null();
}

Node TermDbSygus::getArgConst( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Node > >::iterator itt = d_arg_const.find( tn );
  if( itt!=d_arg_const.end() ){
    std::map< int, Node >::iterator itn = itt->second.find( i );
    if( itn!=itt->second.end() ){
      return itn->second;
    }
  }
  return Node::null();
}

Kind TermDbSygus::getArgKind( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Kind > >::iterator itt = d_arg_kind.find( tn );
  if( itt!=d_arg_kind.end() ){
    std::map< int, Kind >::iterator itk = itt->second.find( i );
    if( itk!=itt->second.end() ){
      return itk->second;
    }
  }
  return UNDEFINED_KIND;
}

bool TermDbSygus::isKindArg( TypeNode tn, int i ) {
  return getArgKind( tn, i )!=UNDEFINED_KIND;
}

bool TermDbSygus::isConstArg( TypeNode tn, int i ) {
  Assert( isRegistered( tn ) );
  std::map< TypeNode, std::map< int, Node > >::iterator itt = d_arg_const.find( tn );
  if( itt!=d_arg_const.end() ){
    return itt->second.find( i )!=itt->second.end();
  }else{
    return false;
  }
}

unsigned TermDbSygus::getNumIdFuncs( TypeNode tn ) {
  return d_id_funcs[tn].size();
}

unsigned TermDbSygus::getIdFuncIndex( TypeNode tn, unsigned i ) {
  return d_id_funcs[tn][i];
}

TypeNode TermDbSygus::getArgType( const DatatypeConstructor& c, int i ) {
  Assert( i>=0 && i<(int)c.getNumArgs() );
  return TypeNode::fromType( ((SelectorType)c[i].getType()).getRangeType() );
}

Node TermDbSygus::minimizeBuiltinTerm( Node n ) {
  if( ( n.getKind()==EQUAL || n.getKind()==LEQ || n.getKind()==LT || n.getKind()==GEQ || n.getKind()==GT ) &&
      ( n[0].getType().isInteger() || n[0].getType().isReal() ) ){
    bool changed = false;
    std::vector< Node > mon[2];
    for( unsigned r=0; r<2; r++ ){
      unsigned ro = r==0 ? 1 : 0;
      Node c;
      Node nc;
      if( n[r].getKind()==PLUS ){
        for( unsigned i=0; i<n[r].getNumChildren(); i++ ){
          if( QuantArith::getMonomial( n[r][i], c, nc ) && c.getConst<Rational>().isNegativeOne() ){
            mon[ro].push_back( nc );
            changed = true;
          }else{
            if( !n[r][i].isConst() || !n[r][i].getConst<Rational>().isZero() ){
              mon[r].push_back( n[r][i] );
            }
          }
        }
      }else{
        if( QuantArith::getMonomial( n[r], c, nc ) && c.getConst<Rational>().isNegativeOne() ){
          mon[ro].push_back( nc );
          changed = true;
        }else{
          if( !n[r].isConst() || !n[r].getConst<Rational>().isZero() ){
            mon[r].push_back( n[r] );
          }
        }
      }
    }
    if( changed ){
      Node nn[2];
      for( unsigned r=0; r<2; r++ ){
        nn[r] = mon[r].size()==0 ? NodeManager::currentNM()->mkConst( Rational(0) ) : ( mon[r].size()==1 ? mon[r][0] : NodeManager::currentNM()->mkNode( PLUS, mon[r] ) );
      }
      return NodeManager::currentNM()->mkNode( n.getKind(), nn[0], nn[1] );
    }
  }
  return n;
}

Node TermDbSygus::expandBuiltinTerm( Node t ){
  if( t.getKind()==EQUAL && ( t[0].getType().isInteger() || t[0].getType().isReal() ) ){
    return NodeManager::currentNM()->mkNode( AND, NodeManager::currentNM()->mkNode( LEQ, t[0], t[1] ),
                                                  NodeManager::currentNM()->mkNode( LEQ, t[1], t[0] ) );
  }else if( t.getKind()==ITE && t.getType().isBoolean() ){
    return NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, t[0], t[1] ),
                                                 NodeManager::currentNM()->mkNode( AND, t[0].negate(), t[2] ) );
  }else if( t.getKind()==IFF ){
    return NodeManager::currentNM()->mkNode( OR, NodeManager::currentNM()->mkNode( AND, t[0], t[1] ),
                                                 NodeManager::currentNM()->mkNode( AND, t[0].negate(), t[1].negate() ) );
  }
  return Node::null();
}


Kind TermDbSygus::getComparisonKind( TypeNode tn ) {
  if( tn.isInteger() || tn.isReal() ){
    return LT;
  }else if( tn.isBitVector() ){
    return BITVECTOR_ULT;
  }else{
    return UNDEFINED_KIND;
  }
}

Kind TermDbSygus::getPlusKind( TypeNode tn, bool is_neg ) {
  if( tn.isInteger() || tn.isReal() ){
    return is_neg ? MINUS : PLUS;
  }else if( tn.isBitVector() ){
    return is_neg ? BITVECTOR_SUB : BITVECTOR_PLUS;
  }else{
    return UNDEFINED_KIND;
  }
}

bool TermDbSygus::doCompare( Node a, Node b, Kind k ) {
  Node com = NodeManager::currentNM()->mkNode( k, a, b );
  com = Rewriter::rewrite( com );
  return com==d_true;
}


void doStrReplace(std::string& str, const std::string& oldStr, const std::string& newStr){
  size_t pos = 0;
  while((pos = str.find(oldStr, pos)) != std::string::npos){
     str.replace(pos, oldStr.length(), newStr);
     pos += newStr.length();
  }
}

Kind TermDbSygus::getOperatorKind( Node op ) {
  Assert( op.getKind()!=BUILTIN );
  if( smt::currentSmtEngine()->isDefinedFunction( op.toExpr() ) ){
    return APPLY;
  }else{
    TypeNode tn = op.getType();
    if( tn.isConstructor() ){
      return APPLY_CONSTRUCTOR;
    }else if( tn.isSelector() ){
      return APPLY_SELECTOR;
    }else if( tn.isTester() ){
      return APPLY_TESTER;
    }else{
      return NodeManager::operatorToKind( op );
    }
  }
}

void TermDbSygus::printSygusTerm( std::ostream& out, Node n, std::vector< Node >& lvs ) {
  if( n.getKind()==APPLY_CONSTRUCTOR ){
    TypeNode tn = n.getType();
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    if( dt.isSygus() ){
      int cIndex = Datatype::indexOf( n.getOperator().toExpr() );
      Assert( !dt[cIndex].getSygusOp().isNull() );
      if( dt[cIndex].getSygusLetBody().isNull() ){
        if( n.getNumChildren()>0 ){
          out << "(";
        }
        Node op = dt[cIndex].getSygusOp();
        if( op.getType().isBitVector() && op.isConst() ){
          //print in the style it was given
          Trace("sygus-print-bvc") << "[Print " << op << " " << dt[cIndex].getName() << "]" << std::endl;
          std::stringstream ss;
          ss << dt[cIndex].getName();
          std::string str = ss.str();
          std::size_t found = str.find_last_of("_");
          Assert( found!=std::string::npos );
          std::string name = std::string( str.begin() + found +1, str.end() );
          out << name;
        }else{
          out << op;
        }
        if( n.getNumChildren()>0 ){
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            out << " ";
            printSygusTerm( out, n[i], lvs );
          }
          out << ")";
        }
      }else{
        std::stringstream let_out;
        //print as let term
        if( dt[cIndex].getNumSygusLetInputArgs()>0 ){
          let_out << "(let (";
        }
        std::vector< Node > subs_lvs;
        std::vector< Node > new_lvs;
        for( unsigned i=0; i<dt[cIndex].getNumSygusLetArgs(); i++ ){
          Node v = Node::fromExpr( dt[cIndex].getSygusLetArg( i ) );
          subs_lvs.push_back( v );
          std::stringstream ss;
          ss << "_l_" << new_lvs.size();
          Node lv = NodeManager::currentNM()->mkBoundVar( ss.str(), v.getType() );
          new_lvs.push_back( lv );
          //map free variables to proper terms
          if( i<dt[cIndex].getNumSygusLetInputArgs() ){
            //it should be printed as a let argument
            let_out << "(";
            let_out << lv << " " << lv.getType() << " ";
            printSygusTerm( let_out, n[i], lvs );
            let_out << ")";
          }
        }
        if( dt[cIndex].getNumSygusLetInputArgs()>0 ){
          let_out << ") ";
        }
        //print the body
        Node let_body = Node::fromExpr( dt[cIndex].getSygusLetBody() );
        let_body = let_body.substitute( subs_lvs.begin(), subs_lvs.end(), new_lvs.begin(), new_lvs.end() );
        new_lvs.insert( new_lvs.end(), lvs.begin(), lvs.end() );
        printSygusTerm( let_out, let_body, new_lvs );
        if( dt[cIndex].getNumSygusLetInputArgs()>0 ){
          let_out << ")";
        }
        //do variable substitutions since ASSUMING : let_vars are interpreted literally and do not represent a class of variables
        std::string lbody = let_out.str();
        for( unsigned i=0; i<dt[cIndex].getNumSygusLetArgs(); i++ ){
          std::stringstream old_str;
          old_str << new_lvs[i];
          std::stringstream new_str;
          if( i>=dt[cIndex].getNumSygusLetInputArgs() ){
            printSygusTerm( new_str, n[i], lvs );
          }else{
            new_str << Node::fromExpr( dt[cIndex].getSygusLetArg( i ) );
          }
          doStrReplace( lbody, old_str.str().c_str(), new_str.str().c_str() );
        }
        out << lbody;
      }
      return;
    }
  }else if( !n.getAttribute(SygusProxyAttribute()).isNull() ){
    out << n.getAttribute(SygusProxyAttribute());
  }else{
    out << n;
  }
}
