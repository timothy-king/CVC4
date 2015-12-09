/*********************                                                        */
/*! \file theory_datatypes.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of datatypes
 **
 ** Implementation of the theory of datatypes.
 **/

#include <map>

#include "base/cvc4_assert.h"
#include "expr/kind.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "smt/boolean_terms.h"
#include "smt/options.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/datatypes/theory_datatypes_type_rules.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_model.h"
#include "theory/type_enumerator.h"
#include "theory/valuation.h"
#include "util/datatype.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;


TheoryDatatypes::TheoryDatatypes(Context* c, UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_DATATYPES, c, u, out, valuation, logicInfo),
  //d_cycle_check(c),
  d_hasSeenCycle(c, false),
  d_infer(c),
  d_infer_exp(c),
  d_notify( *this ),
  d_equalityEngine(d_notify, c, "theory::datatypes::TheoryDatatypes", true),
  d_labels( c ),
  d_selector_apps( c ),
  //d_consEqc( c ),
  d_conflict( c, false ),
  d_collectTermsCache( c ),
  d_consTerms( c ),
  d_selTerms( c ),
  d_singleton_eq( u ){

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_SELECTOR_TOTAL);
  d_equalityEngine.addFunctionKind(kind::DT_SIZE);
  d_equalityEngine.addFunctionKind(kind::DT_HEIGHT_BOUND);
  d_equalityEngine.addFunctionKind(kind::APPLY_TESTER);
  //d_equalityEngine.addFunctionKind(kind::APPLY_UF);

  d_true = NodeManager::currentNM()->mkConst( true );
  d_dtfCounter = 0;

  d_sygus_split = NULL;
  d_sygus_sym_break = NULL;
}

TheoryDatatypes::~TheoryDatatypes() {
}

void TheoryDatatypes::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

TheoryDatatypes::EqcInfo* TheoryDatatypes::getOrMakeEqcInfo( TNode n, bool doMake ){
  if( !hasEqcInfo( n ) ){
    if( doMake ){
      //add to labels
      NodeList* lbl = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                             ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
      d_labels.insertDataFromContextMemory( n, lbl );

      std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
      EqcInfo* ei;
      if( eqc_i!=d_eqc_info.end() ){
        ei = eqc_i->second;
      }else{
        ei = new EqcInfo( getSatContext() );
        d_eqc_info[n] = ei;
      }
      if( n.getKind()==APPLY_CONSTRUCTOR ){
        ei->d_constructor = n;
      }
      //add to selectors
      NodeList* sel = new(getSatContext()->getCMM()) NodeList( true, getSatContext(), false,
                                                               ContextMemoryAllocator<TNode>(getSatContext()->getCMM()) );
      d_selector_apps.insertDataFromContextMemory( n, sel );
      return ei;
    }else{
      return NULL;
    }
  }else{
    std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
    return (*eqc_i).second;
  }
}

TNode TheoryDatatypes::getEqcConstructor( TNode r ) {
  if( r.getKind()==APPLY_CONSTRUCTOR ){
    return r;
  }else{
    EqcInfo * ei = getOrMakeEqcInfo( r, false );
    if( ei && !ei->d_constructor.get().isNull() ){
      return ei->d_constructor.get();
    }else{
      return r;
    }
  }
}

void TheoryDatatypes::check(Effort e) {
  if (done() && !fullEffort(e)) {
    return;
  }
  d_addedLemma = false;

  TimerStat::CodeTimer checkTimer(d_checkTime);

  Trace("datatypes-check") << "Check effort " << e << std::endl;
  while(!done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;
    Trace("datatypes-assert") << "Assert " << fact << std::endl;

    TNode atom CVC4_UNUSED = fact.getKind() == kind::NOT ? fact[0] : fact;

    // extra debug check to make sure that the rewriter did its job correctly
    Assert( atom.getKind() != kind::EQUAL ||
            ( atom[0].getKind() != kind::TUPLE && atom[1].getKind() != kind::TUPLE &&
              atom[0].getKind() != kind::RECORD && atom[1].getKind() != kind::RECORD &&
              atom[0].getKind() != kind::TUPLE_UPDATE && atom[1].getKind() != kind::TUPLE_UPDATE &&
              atom[0].getKind() != kind::RECORD_UPDATE && atom[1].getKind() != kind::RECORD_UPDATE &&
              atom[0].getKind() != kind::TUPLE_SELECT && atom[1].getKind() != kind::TUPLE_SELECT &&
              atom[0].getKind() != kind::RECORD_SELECT && atom[1].getKind() != kind::RECORD_SELECT ),
            "tuple/record escaped into datatypes decision procedure; should have been rewritten away" );

    //assert the fact
    assertFact( fact, fact );
    flushPendingFacts();
  }

  if( e == EFFORT_FULL && !d_conflict && !d_addedLemma && !d_valuation.needCheck() ) {
    //check for cycles
    Assert( d_pending.empty() && d_pending_merge.empty() );
    bool addedFact;
    do {
      checkCycles();
      addedFact = !d_pending.empty() || !d_pending_merge.empty();
      flushPendingFacts();
      if( d_conflict || d_addedLemma ){
        return;
      }
    }while( addedFact );

    //check for splits
    Debug("datatypes-split") << "Check for splits " << e << endl;
    addedFact = false;
    do {
      std::map< TypeNode, Node > rec_singletons;
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
      while( !eqcs_i.isFinished() ){
        Node n = (*eqcs_i);
        TypeNode tn = n.getType();
        if( DatatypesRewriter::isTypeDatatype( tn ) ){
          Trace("datatypes-debug") << "Process equivalence class " << n << std::endl;
          EqcInfo* eqc = getOrMakeEqcInfo( n );
          //if there are more than 1 possible constructors for eqc
          if( !hasLabel( eqc, n ) ){
            Trace("datatypes-debug") << "No constructor..." << std::endl;
            const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
            bool continueProc = true;
            if( dt.isRecursiveSingleton() ){
              Trace("datatypes-debug") << "Check recursive singleton..." << std::endl;
              //handle recursive singleton case
              std::map< TypeNode, Node >::iterator itrs = rec_singletons.find( tn );
              if( itrs!=rec_singletons.end() ){
                Node eq = n.eqNode( itrs->second );
                if( d_singleton_eq.find( eq )==d_singleton_eq.end() ){
                  d_singleton_eq[eq] = true;
                  // get assumptions
                  bool success = true;
                  std::vector< Node > assumptions;
                  //if there is at least one uninterpreted sort occurring within the datatype and the logic is not quantified, add lemmas ensuring cardinality is more than one,
                  //  do not infer the equality if at least one sort was processed.
                  //otherwise, if the logic is quantified, under the assumption that all uninterpreted sorts have cardinality one,
                  //  infer the equality.
                  for( unsigned i=0; i<dt.getNumRecursiveSingletonArgTypes(); i++ ){
                    TypeNode tn = TypeNode::fromType( dt.getRecursiveSingletonArgType( i ) );
                    if( getQuantifiersEngine() ){
                      // under the assumption that the cardinality of this type is one
                      Node a = getSingletonLemma( tn, true );
                      assumptions.push_back( a.negate() );
                    }else{
                      success = false;
                      // assert that the cardinality of this type is more than one
                      getSingletonLemma( tn, false );
                    }
                  }
                  if( success ){
                    Node eq = n.eqNode( itrs->second );
                    assumptions.push_back( eq );
                    Node lemma = assumptions.size()==1 ? assumptions[0] : NodeManager::currentNM()->mkNode( OR, assumptions );
                    Trace("dt-singleton") << "*************Singleton equality lemma " << lemma << std::endl;
                    d_out->lemma( lemma );
                  }
                }
              }else{
                rec_singletons[tn] = n;
              }
              //do splitting for quantified logics (incomplete anyways)
              continueProc = ( getQuantifiersEngine()!=NULL );
            }
            if( continueProc ){
              Trace("datatypes-debug") << "Get possible cons..." << std::endl;
              //all other cases
              std::vector< bool > pcons;
              getPossibleCons( eqc, n, pcons );
              //check if we do not need to resolve the constructor type for this equivalence class.
              // this is if there are no selectors for this equivalence class, its possible values are infinite,
              //  and we are not producing a model, then do not split.
              int consIndex = -1;
              int fconsIndex = -1;
              bool needSplit = true;
              for( unsigned int j=0; j<pcons.size(); j++ ) {
                if( pcons[j] ) {
                  if( consIndex==-1 ){
                    consIndex = j;
                  }
                  if( !dt[ j ].isFinite() ) {
                    if( !eqc || !eqc->d_selectors ){
                      needSplit = false;
                    }
                  }else{
                    if( fconsIndex==-1 ){
                      fconsIndex = j;
                    }
                  }
                }
              }
              //if we want to force an assignment of constructors to all ground eqc
              //d_dtfCounter++;
              if( !needSplit && options::dtForceAssignment() && d_dtfCounter%2==0 ){
                Trace("datatypes-force-assign") << "Force assignment for " << n << std::endl;
                needSplit = true;
                consIndex = fconsIndex!=-1 ? fconsIndex : consIndex;
              }

              if( needSplit && consIndex!=-1 ) {
                //if only one constructor, then this term must be this constructor
                if( dt.getNumConstructors()==1 ){
                  Node t = DatatypesRewriter::mkTester( n, 0, dt );
                  d_pending.push_back( t );
                  d_pending_exp[ t ] = d_true;
                  Trace("datatypes-infer") << "DtInfer : 1-cons : " << t << std::endl;
                  d_infer.push_back( t );
                }else{
                  if( options::dtBinarySplit() ){
                    Node test = DatatypesRewriter::mkTester( n, consIndex, dt );
                    Trace("dt-split") << "*************Split for possible constructor " << dt[consIndex] << " for " << n << endl;
                    test = Rewriter::rewrite( test );
                    NodeBuilder<> nb(kind::OR);
                    nb << test << test.notNode();
                    Node lemma = nb;
                    d_out->lemma( lemma );
                    d_out->requirePhase( test, true );
                  }else{
                    Trace("dt-split") << "*************Split for constructors on " << n <<  endl;
                    std::vector< Node > children;
                    if( dt.isSygus() && d_sygus_split ){
                      std::vector< Node > lemmas;
                      d_sygus_split->getSygusSplits( n, dt, children, lemmas );
                      for( unsigned i=0; i<lemmas.size(); i++ ){
                        Trace("dt-lemma-sygus") << "Dt sygus lemma : " << lemmas[i] << std::endl;
                        d_out->lemma( lemmas[i] );
                      }
                    }else{
                      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
                        Node test = DatatypesRewriter::mkTester( n, i, dt );
                        children.push_back( test );
                      }
                    }
                    Assert( !children.empty() );
                    Node lemma = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::OR, children );
                    Trace("dt-split-debug") << "Split lemma is : " << lemma << std::endl;
                    d_out->lemma( lemma );
                  }
                  return;
                }
              }else{
                Trace("dt-split-debug") << "Do not split constructor for " << n << " : " << n.getType() << " " << dt.getNumConstructors() << std::endl;
              }
            }
          }else{
            Trace("datatypes-debug") << "Has constructor " << eqc->d_constructor.get() << std::endl;
          }
        }
        ++eqcs_i;
      }
      Trace("datatypes-debug") << "Flush pending facts..."  << std::endl;
      addedFact = !d_pending.empty() || !d_pending_merge.empty();
      flushPendingFacts();
      /*
      if( !d_conflict ){
        if( options::dtRewriteErrorSel() ){
          bool innerAddedFact = false;
          do {
            collapseSelectors();
            innerAddedFact = !d_pending.empty() || !d_pending_merge.empty();
            flushPendingFacts();
          }while( !d_conflict && innerAddedFact );
        }
      }
      */
    }while( !d_conflict && addedFact );
    Trace("datatypes-debug") << "Finished. " << d_conflict << std::endl;
    if( !d_conflict ){
      Trace("dt-model-debug") << std::endl;
      printModelDebug("dt-model-debug");
    }
  }

  if( Debug.isOn("datatypes") || Debug.isOn("datatypes-split") ) {
    Notice() << "TheoryDatatypes::check(): done" << endl;
  }
}

void TheoryDatatypes::flushPendingFacts(){
  doPendingMerges();
  if( !d_pending.empty() ){
    int i = 0;
    while( !d_conflict && i<(int)d_pending.size() ){
      Node fact = d_pending[i];
      Node exp = d_pending_exp[ fact ];
      //check to see if we have to communicate it to the rest of the system
      if( mustCommunicateFact( fact, exp ) ){
        Trace("dt-lemma-debug") << "Assert fact " << fact << " with explanation " << exp << std::endl;
        Node lem = fact;
        if( exp.isNull() || exp==d_true ){
          Trace("dt-lemma-debug") << "Trivial explanation." << std::endl;
        }else{
          Trace("dt-lemma-debug") << "Get explanation..." << std::endl;
          Node ee_exp = explain( exp );
          Trace("dt-lemma-debug") << "Explanation : " << ee_exp << std::endl;
          lem = NodeManager::currentNM()->mkNode( OR, ee_exp.negate(), fact );
          lem = Rewriter::rewrite( lem );
        }
        Trace("dt-lemma") << "Datatypes lemma : " << lem << std::endl;
        d_out->lemma( lem );
        d_addedLemma = true;
      }else{
        assertFact( fact, exp );
      }
      i++;
    }
    d_pending.clear();
    d_pending_exp.clear();
  }
}

void TheoryDatatypes::doPendingMerges(){
  if( !d_conflict ){
    //do all pending merges
    int i=0;
    while( i<(int)d_pending_merge.size() ){
      Assert( d_pending_merge[i].getKind()==EQUAL || d_pending_merge[i].getKind()==IFF );
      merge( d_pending_merge[i][0], d_pending_merge[i][1] );
      i++;
    }
  }
  d_pending_merge.clear();
}

void TheoryDatatypes::assertFact( Node fact, Node exp ){
  Assert( d_pending_merge.empty() );
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.assertEquality( atom, polarity, exp );
  }else{
    d_equalityEngine.assertPredicate( atom, polarity, exp );
  }
  doPendingMerges();
  //add to tester if applicable
  if( atom.getKind()==kind::APPLY_TESTER ){
    Node rep = getRepresentative( atom[0] );
    EqcInfo* eqc = getOrMakeEqcInfo( rep, true );
    addTester( fact, eqc, rep );
    if( !d_conflict && polarity ){
      Trace("dt-tester") << "Assert tester : " << atom << std::endl;
      if( d_sygus_sym_break ){
        //Assert( !d_sygus_util->d_conflict );
        d_sygus_sym_break->addTester( atom );
        for( unsigned i=0; i<d_sygus_sym_break->d_lemmas.size(); i++ ){
          Trace("dt-lemma-sygus") << "Sygus symmetry breaking lemma : " << d_sygus_sym_break->d_lemmas[i] << std::endl;
          d_out->lemma( d_sygus_sym_break->d_lemmas[i] );
        }
        d_sygus_sym_break->d_lemmas.clear();
        /*
        if( d_sygus_util->d_conflict ){
          //d_conflict = true;
          if( !d_sygus_util->d_conflictNode.isNull() ){
            std::vector< TNode > assumptions;
            explain( d_sygus_util->d_conflictNode, assumptions );
            d_conflictNode = mkAnd( assumptions );
            Trace("dt-conflict") << "CONFLICT: sygus symmetry breaking conflict : " << d_conflictNode << std::endl;
            d_out->conflict( d_conflictNode );
          }
          return;
        }
        */
      }
    }
  }
  doPendingMerges();
}

void TheoryDatatypes::preRegisterTerm(TNode n) {
  Debug("datatypes-prereg") << "TheoryDatatypes::preRegisterTerm() " << n << endl;
  collectTerms( n );
  switch (n.getKind()) {
  case kind::EQUAL:
    // Add the trigger for equality
    d_equalityEngine.addTriggerEquality(n);
    break;
  case kind::APPLY_TESTER:
    // Get triggered for both equal and dis-equal
    d_equalityEngine.addTriggerPredicate(n);
    break;
  default:
    // Maybe it's a predicate
    if (n.getType().isBoolean()) {
      // Get triggered for both equal and dis-equal
      d_equalityEngine.addTriggerPredicate(n);
    } else {
      // Function applications/predicates
      d_equalityEngine.addTerm(n);
      //d_equalityEngine.addTriggerTerm(n, THEORY_DATATYPES);
    }
    break;
  }
  flushPendingFacts();
}

void TheoryDatatypes::finishInit() {
  if( getQuantifiersEngine() && options::ceGuidedInst() ){
    quantifiers::TermDbSygus * tds = getQuantifiersEngine()->getTermDatabaseSygus();
    Assert( tds!=NULL );
    d_sygus_split = new SygusSplit( tds );
    d_sygus_sym_break = new SygusSymBreak( tds, getSatContext() );
  }
}

Node TheoryDatatypes::expandDefinition(LogicRequest &logicRequest, Node n) {
  switch( n.getKind() ){
  case kind::APPLY_SELECTOR: {
    Node selector = n.getOperator();
    Expr selectorExpr = selector.toExpr();
    Node sel = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, Node::fromExpr( selectorExpr ), n[0] );
    if( options::dtRewriteErrorSel() ){
      return sel;
    }else{
      size_t selectorIndex = Datatype::cindexOf(selectorExpr);
      const Datatype& dt = Datatype::datatypeOf(selectorExpr);
      const DatatypeConstructor& c = dt[selectorIndex];
      Expr tester = c.getTester();
      Node tst = NodeManager::currentNM()->mkNode( kind::APPLY_TESTER, Node::fromExpr( tester ), n[0] );
      tst = Rewriter::rewrite( tst );
      Node n_ret;
      if( tst==d_true ){
        n_ret = sel;
      }else{
        mkExpDefSkolem( selector, n[0].getType(), n.getType() );
        Node sk = NodeManager::currentNM()->mkNode( kind::APPLY_UF, d_exp_def_skolem[ selector ], n[0]  );
        if( tst==NodeManager::currentNM()->mkConst( false ) ){
          n_ret = sk;
        }else{
          n_ret = NodeManager::currentNM()->mkNode( kind::ITE, tst, sel, sk );
        }
      }
      //n_ret = Rewriter::rewrite( n_ret );
      Trace("dt-expand") << "Expand def : " << n << " to " << n_ret << std::endl;
      return n_ret;
    }
  }
    break;
  default:
    return n;
    break;
  }
  Unreachable();
}

void TheoryDatatypes::presolve() {
  Debug("datatypes") << "TheoryDatatypes::presolve()" << endl;
}

Node TheoryDatatypes::ppRewrite(TNode in) {
  Debug("tuprec") << "TheoryDatatypes::ppRewrite(" << in << ")" << endl;

  if(in.getKind() == kind::TUPLE_SELECT) {
    TypeNode t = in[0].getType();
    if(t.hasAttribute(expr::DatatypeTupleAttr())) {
      t = t.getAttribute(expr::DatatypeTupleAttr());
    }
    TypeNode dtt = NodeManager::currentNM()->getDatatypeForTupleRecord(t);
    const Datatype& dt = DatatypeType(dtt.toType()).getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR_TOTAL, Node::fromExpr(dt[0][in.getOperator().getConst<TupleSelect>().getIndex()].getSelector()), in[0]);
  } else if(in.getKind() == kind::RECORD_SELECT) {
    TypeNode t = in[0].getType();
    if(t.hasAttribute(expr::DatatypeRecordAttr())) {
      t = t.getAttribute(expr::DatatypeRecordAttr());
    }
    TypeNode dtt = NodeManager::currentNM()->getDatatypeForTupleRecord(t);
    const Datatype& dt = DatatypeType(dtt.toType()).getDatatype();
    return NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR_TOTAL, Node::fromExpr(dt[0][in.getOperator().getConst<RecordSelect>().getField()].getSelector()), in[0]);
  }

  TypeNode t = in.getType();

  // we only care about tuples and records here
  if(in.getKind() != kind::TUPLE && in.getKind() != kind::TUPLE_UPDATE &&
     in.getKind() != kind::RECORD && in.getKind() != kind::RECORD_UPDATE) {
    if((t.isTuple() || t.isRecord()) && in.hasAttribute(smt::BooleanTermAttr())) {
      Debug("tuprec") << "should map " << in << " of type " << t << " back to " << in.getAttribute(smt::BooleanTermAttr()).getType() << endl;
      Debug("tuprec") << "so " << NodeManager::currentNM()->getDatatypeForTupleRecord(t).getDatatype() << " goes to " << NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getDatatype() << endl;
      if(t.isTuple()) {
        Debug("tuprec") << "current datatype-tuple-attr is " << NodeManager::currentNM()->getDatatypeForTupleRecord(t).getAttribute(expr::DatatypeTupleAttr()) << endl;
        Debug("tuprec") << "setting to " << NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeTupleAttr()) << endl;
        NodeManager::currentNM()->getDatatypeForTupleRecord(t).setAttribute(expr::DatatypeTupleAttr(), NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeTupleAttr()));
      } else {
        Debug("tuprec") << "current datatype-record-attr is " << NodeManager::currentNM()->getDatatypeForTupleRecord(t).getAttribute(expr::DatatypeRecordAttr()) << endl;
        Debug("tuprec") << "setting to " << NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeRecordAttr()) << endl;
        NodeManager::currentNM()->getDatatypeForTupleRecord(t).setAttribute(expr::DatatypeRecordAttr(), NodeManager::currentNM()->getDatatypeForTupleRecord(in.getAttribute(smt::BooleanTermAttr()).getType()).getAttribute(expr::DatatypeRecordAttr()));
      }
    }

    if( in.getKind()==EQUAL ){
      Node nn;
      std::vector< Node > rew;
      if( DatatypesRewriter::checkClash(in[0], in[1], rew) ){
        nn = NodeManager::currentNM()->mkConst(false);
      }else{
        nn = rew.size()==0 ? d_true :
                  ( rew.size()==1 ? rew[0] : NodeManager::currentNM()->mkNode( kind::AND, rew ) );
      }
      return nn;
    }

    // nothing to do
    return in;
  }

  if(t.hasAttribute(expr::DatatypeTupleAttr())) {
    t = t.getAttribute(expr::DatatypeTupleAttr());
  } else if(t.hasAttribute(expr::DatatypeRecordAttr())) {
    t = t.getAttribute(expr::DatatypeRecordAttr());
  }

  // if the type doesn't have an associated datatype, then make one for it
  TypeNode dtt = (t.isTuple() || t.isRecord()) ? NodeManager::currentNM()->getDatatypeForTupleRecord(t) : t;

  const Datatype& dt = DatatypeType(dtt.toType()).getDatatype();

  // now rewrite the expression
  Node n;
  if(in.getKind() == kind::TUPLE || in.getKind() == kind::RECORD) {
    NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
    b << Node::fromExpr(dt[0].getConstructor());
    b.append(in.begin(), in.end());
    n = b;
  } else if(in.getKind() == kind::TUPLE_UPDATE || in.getKind() == kind::RECORD_UPDATE) {
    NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
    b << Node::fromExpr(dt[0].getConstructor());
    size_t size, updateIndex;
    if(in.getKind() == kind::TUPLE_UPDATE) {
      size = t.getNumChildren();
      updateIndex = in.getOperator().getConst<TupleUpdate>().getIndex();
    } else { // kind::RECORD_UPDATE
      const Record& record = t.getConst<Record>();
      size = record.getNumFields();
      updateIndex = record.getIndex(in.getOperator().getConst<RecordUpdate>().getField());
    }
    Debug("tuprec") << "expr is " << in << std::endl;
    Debug("tuprec") << "updateIndex is " << updateIndex << std::endl;
    Debug("tuprec") << "t is " << t << std::endl;
    Debug("tuprec") << "t has arity " << size << std::endl;
    for(size_t i = 0; i < size; ++i) {
      if(i == updateIndex) {
        b << in[1];
        Debug("tuprec") << "arg " << i << " gets updated to " << in[1] << std::endl;
      } else {
        b << NodeManager::currentNM()->mkNode(kind::APPLY_SELECTOR_TOTAL, Node::fromExpr(dt[0][i].getSelector()), in[0]);
        Debug("tuprec") << "arg " << i << " copies " << b[b.getNumChildren() - 1] << std::endl;
      }
    }
    Debug("tuprec") << "builder says " << b << std::endl;
    n = b;
  }

  Assert(!n.isNull());


  Debug("tuprec") << "REWROTE " << in << " to " << n << std::endl;

  return n;
}

void TheoryDatatypes::addSharedTerm(TNode t) {
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm(): "
                     << t << " " << t.getType().isBoolean() << endl;
  //if( t.getType().isBoolean() ){
    //d_equalityEngine.addTriggerPredicate(t, THEORY_DATATYPES);
  //}else{
  d_equalityEngine.addTriggerTerm(t, THEORY_DATATYPES);
  //}
  Debug("datatypes") << "TheoryDatatypes::addSharedTerm() finished" << std::endl;
}

/** propagate */
void TheoryDatatypes::propagate(Effort effort){

}

/** propagate */
bool TheoryDatatypes::propagate(TNode literal){
  Debug("dt::propagate") << "TheoryDatatypes::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("dt::propagate") << "TheoryDatatypes::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  Trace("dt-prop") << "dtPropagate " << literal << std::endl;
  // Propagate out
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}

void TheoryDatatypes::addAssumptions( std::vector<TNode>& assumptions, std::vector<TNode>& tassumptions ) {
  std::vector<TNode> ntassumptions;
  for( unsigned i=0; i<tassumptions.size(); i++ ){
    //flatten AND
    if( tassumptions[i].getKind()==AND ){
      for( unsigned j=0; j<tassumptions[i].getNumChildren(); j++ ){
        explain( tassumptions[i][j], ntassumptions );
      }
    }else{
      if( std::find( assumptions.begin(), assumptions.end(), tassumptions[i] )==assumptions.end() ){
        assumptions.push_back( tassumptions[i] );
      }
    }
  }
  if( !ntassumptions.empty() ){
    addAssumptions( assumptions, ntassumptions );
  }
}

void TheoryDatatypes::explainEquality( TNode a, TNode b, bool polarity, std::vector<TNode>& assumptions ) {
  if( a!=b ){
    std::vector<TNode> tassumptions;
    d_equalityEngine.explainEquality(a, b, polarity, tassumptions);
    addAssumptions( assumptions, tassumptions );
  }
}

void TheoryDatatypes::explainPredicate( TNode p, bool polarity, std::vector<TNode>& assumptions ) {
  std::vector<TNode> tassumptions;
  d_equalityEngine.explainPredicate(p, polarity, tassumptions);
  addAssumptions( assumptions, tassumptions );
}

/** explain */
void TheoryDatatypes::explain(TNode literal, std::vector<TNode>& assumptions){
  Debug("datatypes-explain") << "Explain " << literal << std::endl;
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    explainEquality( atom[0], atom[1], polarity, assumptions );
  } else if( atom.getKind() == kind::AND && polarity ){
    for( unsigned i=0; i<atom.getNumChildren(); i++ ){
      explain( atom[i], assumptions );
    }
  } else {
    Assert( atom.getKind()!=kind::AND );
    explainPredicate( atom, polarity, assumptions );
  }
}

Node TheoryDatatypes::explain( TNode literal ){
  std::vector< TNode > assumptions;
  explain( literal, assumptions );
  return mkAnd( assumptions );
}

Node TheoryDatatypes::explain( std::vector< Node >& lits ) {
  std::vector< TNode > assumptions;
  for( unsigned i=0; i<lits.size(); i++ ){
    explain( lits[i], assumptions );
  }
  return mkAnd( assumptions );
}

/** Conflict when merging two constants */
void TheoryDatatypes::conflict(TNode a, TNode b){
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain( a.iffNode(b) );
  } else {
    d_conflictNode = explain( a.eqNode(b) );
  }
  Trace("dt-conflict") << "CONFLICT: Eq engine conflict : " << d_conflictNode << std::endl;
  d_out->conflict( d_conflictNode );
  d_conflict = true;
}

/** called when a new equivalance class is created */
void TheoryDatatypes::eqNotifyNewClass(TNode t){
  if( t.getKind()==APPLY_CONSTRUCTOR ){
    getOrMakeEqcInfo( t, true );
    //look at all equivalence classes with constructor terms
/*
    for( BoolMap::const_iterator it = d_consEqc.begin(); it != d_consEqc.end(); ++it ){
      if( (*it).second ){
        TNode r = (*it).first;
        if( r.getType()==t.getType() ){
          EqcInfo * ei = getOrMakeEqcInfo( r, false );
          if( ei && !ei->d_constructor.get().isNull() && ei->d_constructor.get().getOperator()!=t.getOperator() ){
            Node deq = ei->d_constructor.get().eqNode( t ).negate();
            d_pending.push_back( deq );
            d_pending_exp[ deq ] = d_true;
            Trace("datatypes-infer") << "DtInfer : diff constructor : " << deq << std::endl;
            d_infer.push_back( deq );
          }
        }
      }
    }
*/
    //d_consEqc[t] = true;
  }
}

/** called when two equivalance classes will merge */
void TheoryDatatypes::eqNotifyPreMerge(TNode t1, TNode t2){

}

/** called when two equivalance classes have merged */
void TheoryDatatypes::eqNotifyPostMerge(TNode t1, TNode t2){
  if( DatatypesRewriter::isTermDatatype( t1 ) ){
    d_pending_merge.push_back( t1.eqNode( t2 ) );
  }
}

void TheoryDatatypes::merge( Node t1, Node t2 ){
  if( !d_conflict ){
    TNode trep1 = t1;
    TNode trep2 = t2;
    Debug("datatypes-debug") << "Merge " << t1 << " " << t2 << std::endl;
    EqcInfo* eqc2 = getOrMakeEqcInfo( t2 );
    if( eqc2 ){
      bool checkInst = false;
      if( !eqc2->d_constructor.get().isNull() ){
        trep2 = eqc2->d_constructor.get();
      }
      EqcInfo* eqc1 = getOrMakeEqcInfo( t1 );
      if( eqc1 ){
        if( !eqc1->d_constructor.get().isNull() ){
          trep1 = eqc1->d_constructor.get();
        }
        //check for clash
        TNode cons1 = eqc1->d_constructor.get();
        TNode cons2 = eqc2->d_constructor.get();
        //if both have constructor, then either clash or unification
        if( !cons1.isNull() && !cons2.isNull() ){
          Debug("datatypes-debug") << "Constructors : " << cons1 << " " << cons2 << std::endl;
          Node unifEq = cons1.eqNode( cons2 );
          /*
          std::vector< Node > exp;
          std::vector< std::pair< TNode, TNode > > deq_cand;
          bool conf = checkClashModEq( cons1, cons2, exp, deq_cand );
          if( !conf ){
            for( unsigned i=0; i<deq_cand.size(); i++ ){
              if( d_equalityEngine.areDisequal( deq_cand[i].first, deq_cand[i].second, true ) ){
                conf = true;
                Node eq = NodeManager::currentNM()->mkNode( deq_cand[i].first.getType().isBoolean() ? kind::IFF : kind::EQUAL,
                                                            deq_cand[i].first, deq_cand[i].second );
                exp.push_back( eq.negate() );
              }
            }
          }
          if( conf ){
            exp.push_back( unifEq );
            d_conflictNode = explain( exp );
         */
          std::vector< Node > rew;
          if( DatatypesRewriter::checkClash( cons1, cons2, rew ) ){
            d_conflictNode = explain( unifEq );
            Trace("dt-conflict") << "CONFLICT: Clash conflict : " << d_conflictNode << std::endl;
            d_out->conflict( d_conflictNode );
            d_conflict = true;
            return;
          }else{

            //do unification
            for( int i=0; i<(int)cons1.getNumChildren(); i++ ) {
              if( !areEqual( cons1[i], cons2[i] ) ){
                Node eq = cons1[i].getType().isBoolean() ? cons1[i].iffNode( cons2[i] ) : cons1[i].eqNode( cons2[i] );
                d_pending.push_back( eq );
                d_pending_exp[ eq ] = unifEq;
                Trace("datatypes-infer") << "DtInfer : cons-inj : " << eq << " by " << unifEq << std::endl;
                d_infer.push_back( eq );
                d_infer_exp.push_back( unifEq );
              }
            }
/*
            for( unsigned i=0; i<rew.size(); i++ ){
              d_pending.push_back( rew[i] );
              d_pending_exp[ rew[i] ] = unifEq;
              Trace("datatypes-infer") << "DtInfer : cons-inj : " << rew[i] << " by " << unifEq << std::endl;
              d_infer.push_back( rew[i] );
              d_infer_exp.push_back( unifEq );
            }
*/
          }
        }
        if( !eqc1->d_inst && eqc2->d_inst ){
          eqc1->d_inst = true;
        }
        if( !cons2.isNull() ){
          if( cons1.isNull() ){
            Debug("datatypes-debug") << "Must check if it is okay to set the constructor." << std::endl;
            checkInst = true;
            addConstructor( eqc2->d_constructor.get(), eqc1, t1 );
            if( d_conflict ){
              return;
            }
            //d_consEqc[t1] = true;
          }
          //d_consEqc[t2] = false;
        }
      }else{
        Debug("datatypes-debug") << "No eqc info for " << t1 << ", must create" << std::endl;
        //just copy the equivalence class information
        eqc1 = getOrMakeEqcInfo( t1, true );
        eqc1->d_inst.set( eqc2->d_inst );
        eqc1->d_constructor.set( eqc2->d_constructor );
        eqc1->d_selectors.set( eqc2->d_selectors );
      }


      //merge labels
      NodeListMap::iterator lbl_i = d_labels.find( t2 );
      if( lbl_i != d_labels.end() ){
        Debug("datatypes-debug") << "Merge labels from " << eqc2 << " " << t2 << std::endl;
        NodeList* lbl = (*lbl_i).second;
        for( NodeList::const_iterator j = lbl->begin(); j != lbl->end(); ++j ){
          addTester( *j, eqc1, t1 );
          if( d_conflict ){
            Debug("datatypes-debug") << "Conflict!" << std::endl;
            return;
          }
        }
      }
      //merge selectors
      if( !eqc1->d_selectors && eqc2->d_selectors ){
        eqc1->d_selectors = true;
        checkInst = true;
      }
      NodeListMap::iterator sel_i = d_selector_apps.find( t2 );
      if( sel_i != d_selector_apps.end() ){
        Debug("datatypes-debug") << "Merge selectors from " << eqc2 << " " << t2 << std::endl;
        NodeList* sel = (*sel_i).second;
        for( NodeList::const_iterator j = sel->begin(); j != sel->end(); ++j ){
          addSelector( *j, eqc1, t1, eqc2->d_constructor.get().isNull() );
        }
      }
      if( checkInst ){
        instantiate( eqc1, t1 );
        if( d_conflict ){
          return;
        }
      }
    }
  }
}

/** called when two equivalence classes are made disequal */
void TheoryDatatypes::eqNotifyDisequal(TNode t1, TNode t2, TNode reason){

}

TheoryDatatypes::EqcInfo::EqcInfo( context::Context* c ) :
d_inst( c, false ), d_constructor( c, Node::null() ), d_selectors( c, false ){

}

bool TheoryDatatypes::hasLabel( EqcInfo* eqc, Node n ){
  return ( eqc && !eqc->d_constructor.get().isNull() ) || !getLabel( n ).isNull();
}

Node TheoryDatatypes::getLabel( Node n ) {
  NodeListMap::iterator lbl_i = d_labels.find( n );
  if( lbl_i != d_labels.end() ){
    NodeList* lbl = (*lbl_i).second;
    if( !(*lbl).empty() && (*lbl)[ (*lbl).size() - 1 ].getKind()==kind::APPLY_TESTER ){
      return (*lbl)[ (*lbl).size() - 1 ];
    }
  }
  return Node::null();
}

int TheoryDatatypes::getLabelIndex( EqcInfo* eqc, Node n ){
  if( eqc && !eqc->d_constructor.get().isNull() ){
    return Datatype::indexOf( eqc->d_constructor.get().getOperator().toExpr() );
  }else{
    return Datatype::indexOf( getLabel( n ).getOperator().toExpr() );
  }
}

bool TheoryDatatypes::hasTester( Node n ) {
  NodeListMap::iterator lbl_i = d_labels.find( n );
  if( lbl_i != d_labels.end() ){
    return !(*(*lbl_i).second).empty();
  }else{
    return false;
  }
}

void TheoryDatatypes::getPossibleCons( EqcInfo* eqc, Node n, std::vector< bool >& pcons ){
  const Datatype& dt = ((DatatypeType)(n.getType()).toType()).getDatatype();
  pcons.resize( dt.getNumConstructors(), !hasLabel( eqc, n ) );
  if( hasLabel( eqc, n ) ){
    pcons[ getLabelIndex( eqc, n ) ] = true;
  }else{
    NodeListMap::iterator lbl_i = d_labels.find( n );
    if( lbl_i != d_labels.end() ){
      NodeList* lbl = (*lbl_i).second;
      for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
        Assert( (*i).getKind()==NOT );
        pcons[ Datatype::indexOf( (*i)[0].getOperator().toExpr() ) ] = false;
      }
    }
  }
}

void TheoryDatatypes::mkExpDefSkolem( Node sel, TypeNode dt, TypeNode rt ) {
  if( d_exp_def_skolem.find( sel )==d_exp_def_skolem.end() ){
    std::stringstream ss;
    ss << sel << "_uf";
    d_exp_def_skolem[ sel ] = NodeManager::currentNM()->mkSkolem( ss.str().c_str(),
                                  NodeManager::currentNM()->mkFunctionType( dt, rt ) );
  }
}

void TheoryDatatypes::addTester( Node t, EqcInfo* eqc, Node n ){
  Debug("datatypes-debug") << "Add tester : " << t << " to eqc(" << n << ")" << std::endl;
  Debug("datatypes-labels") << "Add tester " << t << " " << n << " " << eqc << std::endl;
  bool tpolarity = t.getKind()!=NOT;
  Node tt = ( t.getKind() == NOT ) ? t[0] : t;
  int ttindex = Datatype::indexOf( tt.getOperator().toExpr() );
  Node j, jt;
  bool makeConflict = false;
  if( hasLabel( eqc, n ) ){
    //if we already know the constructor type, check whether it is in conflict or redundant
    int jtindex = getLabelIndex( eqc, n );
    if( (jtindex==ttindex)!=tpolarity ){
      if( !eqc->d_constructor.get().isNull() ){
        //conflict because equivalence class contains a constructor
        std::vector< TNode > assumptions;
        explain( t, assumptions );
        explainEquality( eqc->d_constructor.get(), tt[0], true, assumptions );
        d_conflictNode = mkAnd( assumptions );
        Trace("dt-conflict") << "CONFLICT: Tester eq conflict : " << d_conflictNode << std::endl;
        d_out->conflict( d_conflictNode );
        d_conflict = true;
        return;
      }else{
        makeConflict = true;
        //conflict because the existing label is contradictory
        j = getLabel( n );
        jt = j;
      }
    }else{
      return;
    }
  }else{
    //otherwise, scan list of labels
    NodeListMap::iterator lbl_i = d_labels.find( n );
    Assert( lbl_i != d_labels.end() );
    NodeList* lbl = (*lbl_i).second;
    for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
      Assert( (*i).getKind()==NOT );
      j = *i;
      jt = j[0];
      int jtindex = Datatype::indexOf( jt.getOperator().toExpr() );
      if( jtindex==ttindex ){
        if( tpolarity ){  //we are in conflict
          makeConflict = true;
          break;
        }else{            //it is redundant
          return;
        }
      }
    }
    if( !makeConflict ){
      Debug("datatypes-labels") << "Add to labels " << t << std::endl;
      lbl->push_back( t );
      const Datatype& dt = ((DatatypeType)(tt[0].getType()).toType()).getDatatype();
      Debug("datatypes-labels") << "Labels at " << lbl->size() << " / " << dt.getNumConstructors() << std::endl;
      if( tpolarity ){
        instantiate( eqc, n );
      }else{
        //check if we have reached the maximum number of testers
        // in this case, add the positive tester
        //this should not be done for sygus, since cases may be limited
        if( lbl->size()==dt.getNumConstructors()-1 && !dt.isSygus() ){
          std::vector< bool > pcons;
          getPossibleCons( eqc, n, pcons );
          int testerIndex = -1;
          for( int i=0; i<(int)pcons.size(); i++ ) {
            if( pcons[i] ){
              testerIndex = i;
              break;
            }
          }
          Assert( testerIndex!=-1 );
          //we must explain why each term in the set of testers for this equivalence class is equal
          std::vector< Node > eq_terms;
          NodeBuilder<> nb(kind::AND);
          for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
            nb << (*i);
            if( std::find( eq_terms.begin(), eq_terms.end(), (*i)[0][0] )==eq_terms.end() ){
              eq_terms.push_back( (*i)[0][0] );
              if( (*i)[0][0]!=tt[0] ){
                nb << (*i)[0][0].eqNode( tt[0] );
              }
            }
          }
          Node t_concl = DatatypesRewriter::mkTester( tt[0], testerIndex, dt );
          Node t_concl_exp = ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
          d_pending.push_back( t_concl );
          d_pending_exp[ t_concl ] = t_concl_exp;
          Trace("datatypes-infer") << "DtInfer : label : " << t_concl << " by " << t_concl_exp << std::endl;
          d_infer.push_back( t_concl );
          d_infer_exp.push_back( t_concl_exp );
          return;
        }
      }
    }
  }
  if( makeConflict ){
    d_conflict = true;
    Debug("datatypes-labels") << "Explain " << j << " " << t << std::endl;
    std::vector< TNode > assumptions;
    explain( j, assumptions );
    explain( t, assumptions );
    explainEquality( jt[0], tt[0], true, assumptions );
    d_conflictNode = mkAnd( assumptions );
    Trace("dt-conflict") << "CONFLICT: Tester conflict : " << d_conflictNode << std::endl;
    d_out->conflict( d_conflictNode );
  }
}

void TheoryDatatypes::addSelector( Node s, EqcInfo* eqc, Node n, bool assertFacts ) {
  Trace("dt-collapse-sel") << "Add selector : " << s << " to eqc(" << n << ")" << std::endl;
  //check to see if it is redundant
  NodeListMap::iterator sel_i = d_selector_apps.find( n );
  Assert( sel_i != d_selector_apps.end() );
  if( sel_i != d_selector_apps.end() ){
    NodeList* sel = (*sel_i).second;
    for( NodeList::const_iterator j = sel->begin(); j != sel->end(); ++j ){
      Node ss = *j;
      if( s.getOperator()==ss.getOperator() && ( s.getKind()!=DT_HEIGHT_BOUND || s[1]==ss[1] ) ){
        Trace("dt-collapse-sel") << "...redundant." << std::endl;
        return;
      }
    }
    //add it to the vector
    sel->push_back( s );
    eqc->d_selectors = true;
  }
  if( assertFacts && !eqc->d_constructor.get().isNull() ){
    //conclude the collapsed merge
    collapseSelector( s, eqc->d_constructor.get() );
  }
}

void TheoryDatatypes::addConstructor( Node c, EqcInfo* eqc, Node n ){
  Debug("datatypes-debug") << "Add constructor : " << c << " to eqc(" << n << ")" << std::endl;
  Assert( eqc->d_constructor.get().isNull() );
  //check labels
  NodeListMap::iterator lbl_i = d_labels.find( n );
  if( lbl_i != d_labels.end() ){
    size_t constructorIndex = Datatype::indexOf(c.getOperator().toExpr());
    NodeList* lbl = (*lbl_i).second;
    for( NodeList::const_iterator i = lbl->begin(); i != lbl->end(); i++ ) {
      if( (*i).getKind()==NOT ){
        if( Datatype::indexOf( (*i)[0].getOperator().toExpr() )==constructorIndex ){
          Node n = *i;
          std::vector< TNode > assumptions;
          explain( *i, assumptions );
          explainEquality( c, (*i)[0][0], true, assumptions );
          d_conflictNode = mkAnd( assumptions );
          Trace("dt-conflict") << "CONFLICT: Tester merge eq conflict : " << d_conflictNode << std::endl;
          d_out->conflict( d_conflictNode );
          d_conflict = true;
          return;
        }
      }
    }
  }
  //check selectors
  NodeListMap::iterator sel_i = d_selector_apps.find( n );
  if( sel_i != d_selector_apps.end() ){
    NodeList* sel = (*sel_i).second;
    for( NodeList::const_iterator j = sel->begin(); j != sel->end(); ++j ){
      //collapse the selector
      collapseSelector( *j, c );
    }
  }
  eqc->d_constructor.set( c );
}

void TheoryDatatypes::collapseSelector( Node s, Node c ) {
  Assert( c.getKind()==APPLY_CONSTRUCTOR );
  Trace("dt-collapse-sel") << "collapse selector : " << s << " " << c << std::endl;
  Node r;
  bool wrong = false;
  if( s.getKind()==kind::APPLY_SELECTOR_TOTAL ){
    //Trace("dt-collapse-sel") << "Indices : " << Datatype::indexOf(c.getOperator().toExpr()) << " " << Datatype::cindexOf(s.getOperator().toExpr()) << std::endl;
    wrong = Datatype::indexOf(c.getOperator().toExpr())!=Datatype::cindexOf(s.getOperator().toExpr());
    //if( wrong ){
    //  return;
    //}
    //if( Datatype::indexOf(c.getOperator().toExpr())!=Datatype::cindexOf(s.getOperator().toExpr()) ){
    //  mkExpDefSkolem( s.getOperator(), s[0].getType(), s.getType() );
    //  r = NodeManager::currentNM()->mkNode( kind::APPLY_UF, d_exp_def_skolem[s.getOperator().toExpr()], s[0] );
    //}else{
    r = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, s.getOperator(), c );
  }else{
    if( s.getKind()==DT_SIZE ){
      r = NodeManager::currentNM()->mkNode( DT_SIZE, c );
    }else if( s.getKind()==DT_HEIGHT_BOUND ){
      r = NodeManager::currentNM()->mkNode( DT_HEIGHT_BOUND, c, s[1] );
      if( r==d_true ){
        return;
      }
    }
  }
  if( !r.isNull() ){
    Node rr = Rewriter::rewrite( r );
    if( s!=rr ){
      Node eq_exp = c.eqNode( s[0] );
      Node eq = rr.getType().isBoolean() ? s.iffNode( rr ) : s.eqNode( rr );
      Trace("datatypes-infer") << "DtInfer : collapse sel";
      Trace("datatypes-infer") << ( wrong ? " wrong" : "");
      Trace("datatypes-infer") << " : " << eq << " by " << eq_exp << std::endl;

      d_pending.push_back( eq );
      d_pending_exp[ eq ] = eq_exp;
      d_infer.push_back( eq );
      d_infer_exp.push_back( eq_exp );
    }
  }
}

EqualityStatus TheoryDatatypes::getEqualityStatus(TNode a, TNode b){
  Assert(d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b));
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  return EQUALITY_FALSE_IN_MODEL;
}

void TheoryDatatypes::computeCareGraph(){
  Trace("dt-cg") << "Compute graph for dt..." << std::endl;
  vector< pair<TNode, TNode> > currentPairs;
  for( unsigned r=0; r<2; r++ ){
    unsigned functionTerms = r==0 ? d_consTerms.size() : d_selTerms.size();
    for( unsigned i=0; i<functionTerms; i++ ){
      TNode f1 = r==0 ? d_consTerms[i] : d_selTerms[i];
      Assert(d_equalityEngine.hasTerm(f1));
      for( unsigned j=i+1; j<functionTerms; j++ ){
        TNode f2 = r==0 ? d_consTerms[j] : d_selTerms[j];
        Trace("dt-cg-debug") << "dt-cg(" << r << "): " << f1 << " and " << f2 << " " << (f1.getOperator()==f2.getOperator()) << " " << areEqual( f1, f2 ) << std::endl;
        Assert(d_equalityEngine.hasTerm(f2));
        if( f1.getOperator()==f2.getOperator() &&
            ( ( f1.getKind()!=DT_SIZE && f1.getKind()!=DT_HEIGHT_BOUND ) || f1[0].getType()==f2[0].getType() ) &&
            !areEqual( f1, f2 ) ){
          Trace("dt-cg") << "Check " << f1 << " and " << f2 << std::endl;
          bool somePairIsDisequal = false;
          currentPairs.clear();
          for (unsigned k = 0; k < f1.getNumChildren(); ++ k) {
            TNode x = f1[k];
            TNode y = f2[k];
            Assert(d_equalityEngine.hasTerm(x));
            Assert(d_equalityEngine.hasTerm(y));
            if( areDisequal(x, y) ){
              somePairIsDisequal = true;
              break;
            }else if( !d_equalityEngine.areEqual( x, y ) ){
              Trace("dt-cg") << "Arg #" << k << " is " << x << " " << y << std::endl;
              if( d_equalityEngine.isTriggerTerm(x, THEORY_DATATYPES) && d_equalityEngine.isTriggerTerm(y, THEORY_DATATYPES) ){
                TNode x_shared = d_equalityEngine.getTriggerTermRepresentative(x, THEORY_DATATYPES);
                TNode y_shared = d_equalityEngine.getTriggerTermRepresentative(y, THEORY_DATATYPES);
                Trace("dt-cg") << "Arg #" << k << " shared term is " << x_shared << " " << y_shared << std::endl;
                EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
                Trace("dt-cg") << "...eq status is " << eqStatus << std::endl;
                if( eqStatus==EQUALITY_FALSE_AND_PROPAGATED || eqStatus==EQUALITY_FALSE || eqStatus==EQUALITY_FALSE_IN_MODEL ){
                  somePairIsDisequal = true;
                  break;
                }else{
                  currentPairs.push_back(make_pair(x_shared, y_shared));
                }
              }
            }
          }
          if (!somePairIsDisequal) {
            for (unsigned c = 0; c < currentPairs.size(); ++ c) {
              Trace("dt-cg-pair") << "Pair : " << currentPairs[c].first << " " << currentPairs[c].second << std::endl;
              addCarePair(currentPairs[c].first, currentPairs[c].second);
            }
          }
        }
      }
    }
  }
  Trace("dt-cg") << "Done Compute graph for dt." << std::endl;
}

void TheoryDatatypes::collectModelInfo( TheoryModel* m, bool fullModel ){
  Trace("dt-cmi") << "Datatypes : Collect model info " << d_equalityEngine.consistent() << std::endl;
  Trace("dt-model") << std::endl;
  printModelDebug( "dt-model" );
  Trace("dt-model") << std::endl;

  //combine the equality engine
  m->assertEqualityEngine( &d_equalityEngine );

  //get all constructors
  eq::EqClassesIterator eqccs_i = eq::EqClassesIterator( &d_equalityEngine );
  std::vector< Node > cons;
  std::vector< Node > nodes;
  std::map< Node, Node > eqc_cons;
  while( !eqccs_i.isFinished() ){
    Node eqc = (*eqccs_i);
    //for all equivalence classes that are datatypes
    if( DatatypesRewriter::isTermDatatype( eqc ) ){
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      if( ei && !ei->d_constructor.get().isNull() ){
        Node c = ei->d_constructor.get();
        cons.push_back( c );
        eqc_cons[ eqc ] = c;
      }else{
        //if eqc contains a symbol known to datatypes (a selector), then we must assign
        //should assign constructors to EQC if they have a selector or a tester
        bool shouldConsider = ( ei && ei->d_selectors ) || hasTester( eqc );
        if( shouldConsider ){
          nodes.push_back( eqc );
        }
      }
    }
    ++eqccs_i;
  }

  //unsigned orig_size = nodes.size();
  std::map< TypeNode, int > typ_enum_map;
  std::vector< TypeEnumerator > typ_enum;
  unsigned index = 0;
  while( index<nodes.size() ){
    Node eqc = nodes[index];
    Node neqc;
    bool addCons = false;
    const Datatype& dt = ((DatatypeType)(eqc.getType()).toType()).getDatatype();
    if( !d_equalityEngine.hasTerm( eqc ) ){
      Assert( false );
      /*
      if( !dt.isCodatatype() ){
        Trace("dt-cmi") << "NOTICE : Datatypes: need to assign constructor for " << eqc << std::endl;
        Trace("dt-cmi") << "   Type : " << eqc.getType() << std::endl;
        TypeNode tn = eqc.getType();
        //if it is infinite, make sure it is fresh
        //  this ensures that the term that this is an argument of is distinct.
        if( eqc.getType().getCardinality().isInfinite() ){
          std::map< TypeNode, int >::iterator it = typ_enum_map.find( tn );
          int teIndex;
          if( it==typ_enum_map.end() ){
            teIndex = (int)typ_enum.size();
            typ_enum_map[tn] = teIndex;
            typ_enum.push_back( TypeEnumerator(tn) );
          }else{
            teIndex = it->second;
          }
          bool success;
          do{
            success = true;
            Assert( !typ_enum[teIndex].isFinished() );
            neqc = *typ_enum[teIndex];
            Trace("dt-cmi-debug") << "Try " << neqc << " ... " << std::endl;
            ++typ_enum[teIndex];
            for( unsigned i=0; i<cons.size(); i++ ){
              //check if it is modulo equality the same
              if( cons[i].getOperator()==neqc.getOperator() ){
                bool diff = false;
                for( unsigned j=0; j<cons[i].getNumChildren(); j++ ){
                  if( !m->areEqual( cons[i][j], neqc[j] ) ){
                    diff = true;
                    break;
                  }
                }
                if( !diff ){
                  Trace("dt-cmi-debug") << "...Already equivalent modulo equality to " << cons[i] << std::endl;
                  success = false;
                  break;
                }
              }
            }
          }while( !success );
        }else{
          TypeEnumerator te(tn);
          neqc = *te;
        }
      }
      */
    }else{
      Trace("dt-cmi") << "NOTICE : Datatypes: no constructor in equivalence class " << eqc << std::endl;
      Trace("dt-cmi") << "   Type : " << eqc.getType() << std::endl;
      EqcInfo* ei = getOrMakeEqcInfo( eqc );
      std::vector< bool > pcons;
      getPossibleCons( ei, eqc, pcons );
      Trace("dt-cmi") << "Possible constructors : ";
      for( unsigned i=0; i<pcons.size(); i++ ){
        Trace("dt-cmi") << pcons[i] << " ";
      }
      Trace("dt-cmi") << std::endl;
      for( unsigned r=0; r<2; r++ ){
        if( neqc.isNull() ){
          for( unsigned i=0; i<pcons.size(); i++ ){
            //must try the infinite ones first
            if( pcons[i] && (r==1)==dt[ i ].isFinite() ){
              neqc = DatatypesRewriter::getInstCons( eqc, dt, i );
              //for( unsigned j=0; j<neqc.getNumChildren(); j++ ){
              //  //if( sels[i].find( j )==sels[i].end() && DatatypesRewriter::isTermDatatype( neqc[j] ) ){
              //  if( !d_equalityEngine.hasTerm( neqc[j] ) && DatatypesRewriter::isTermDatatype( neqc[j] ) ){
              //    nodes.push_back( neqc[j] );
              //  }
              //}
              break;
            }
          }
        }
      }
      addCons = true;
    }
    if( !neqc.isNull() ){
      Trace("dt-cmi") << "Assign : " << neqc << std::endl;
      m->assertEquality( eqc, neqc, true );
      eqc_cons[ eqc ] = neqc;
    }
    if( addCons ){
      cons.push_back( neqc );
    }
    ++index;
  }

  for( std::map< Node, Node >::iterator it = eqc_cons.begin(); it != eqc_cons.end(); ++it ){
    Node eqc = it->first;
    if( eqc.getType().isCodatatype() ){
      //until models are implemented for codatatypes
      //throw Exception("Models for codatatypes are not supported in this version.");
      //must proactive expand to avoid looping behavior in model builder
      std::map< Node, int > vmap;
      Node v = getCodatatypesValue( it->first, eqc_cons, vmap, 0 );
      Trace("dt-cmi") << "  EQC(" << it->first << "), constructor is " << it->second << ", value is " << v << ", const = " << v.isConst() << std::endl;
      m->assertEquality( eqc, v, true );
      m->assertRepresentative( v );
    }else{
      Trace("dt-cmi") << "Datatypes : assert representative " << it->second << " for " << it->first << std::endl;
      m->assertRepresentative( it->second );
    }
  }
}


Node TheoryDatatypes::getCodatatypesValue( Node n, std::map< Node, Node >& eqc_cons, std::map< Node, int >& vmap, int depth ){
  std::map< Node, int >::iterator itv = vmap.find( n );
  if( itv!=vmap.end() ){
    int debruijn = depth - 1 - itv->second;
    return NodeManager::currentNM()->mkConst(UninterpretedConstant(n.getType().toType(), debruijn));
  }else if( DatatypesRewriter::isTermDatatype( n ) ){
    Node nc = eqc_cons[n];
    if( !nc.isNull() ){
      vmap[n] = depth;
      Trace("dt-cmi-cdt-debug") << "    map " << n << " -> " << depth << std::endl;
      Assert( nc.getKind()==APPLY_CONSTRUCTOR );
      std::vector< Node > children;
      children.push_back( nc.getOperator() );
      for( unsigned i=0; i<nc.getNumChildren(); i++ ){
        Node r = getRepresentative( nc[i] );
        Node rv = getCodatatypesValue( r, eqc_cons, vmap, depth+1 );
        children.push_back( rv );
      }
      vmap.erase( n );
      return NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
    }
  }
  return n;
}

Node TheoryDatatypes::getSingletonLemma( TypeNode tn, bool pol ) {
  int index = pol ? 0 : 1;
  std::map< TypeNode, Node >::iterator it = d_singleton_lemma[index].find( tn );
  if( it==d_singleton_lemma[index].end() ){
    Node a;
    if( pol ){
      Node v1 = NodeManager::currentNM()->mkBoundVar( tn );
      Node v2 = NodeManager::currentNM()->mkBoundVar( tn );
      a = NodeManager::currentNM()->mkNode( FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, v1, v2 ), v1.eqNode( v2 ) );
    }else{
      Node v1 = NodeManager::currentNM()->mkSkolem( "k1", tn );
      Node v2 = NodeManager::currentNM()->mkSkolem( "k2", tn );
      a = v1.eqNode( v2 ).negate();
      //send out immediately as lemma
      d_out->lemma( a );
      Trace("dt-singleton") << "******** assert " << a << " to avoid singleton cardinality for type " << tn << std::endl;
    }
    d_singleton_lemma[index][tn] = a;
    return a;
  }else{
    return it->second;
  }
}

void TheoryDatatypes::collectTerms( Node n ) {
  if( d_collectTermsCache.find( n )==d_collectTermsCache.end() ){
    d_collectTermsCache[n] = true;
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      collectTerms( n[i] );
    }
    if( n.getKind() == APPLY_CONSTRUCTOR ){
      Debug("datatypes") << "  Found constructor " << n << endl;
      d_consTerms.push_back( n );
    }else if( n.getKind() == APPLY_SELECTOR_TOTAL || n.getKind() == DT_SIZE || n.getKind() == DT_HEIGHT_BOUND ){
      d_selTerms.push_back( n );
      //we must also record which selectors exist
      Trace("dt-collapse-sel") << "  Found selector " << n << endl;
      Node rep = getRepresentative( n[0] );
      //record it in the selectors
      EqcInfo* eqc = getOrMakeEqcInfo( rep, true );
      //add it to the eqc info
      addSelector( n, eqc, rep );

      if( n.getKind() == DT_SIZE ){
        Node conc = NodeManager::currentNM()->mkNode( LEQ, NodeManager::currentNM()->mkConst( Rational(0) ), n );
        //must be non-negative
        Trace("datatypes-infer") << "DtInfer : non-negative size : " << conc << std::endl;
        d_pending.push_back( conc );
        d_pending_exp[ conc ] = d_true;
        d_infer.push_back( conc );
/*
        //add size = 0 lemma
        Node nn = n.eqNode( NodeManager::currentNM()->mkConst( Rational(0) ) );
        std::vector< Node > children;
        children.push_back( nn.negate() );
        const Datatype& dt = ((DatatypeType)(n[0].getType()).toType()).getDatatype();
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          if( DatatypesRewriter::isNullaryConstructor( dt[i] ) ){
            Node test = DatatypesRewriter::mkTester( n[0], i, dt );
            children.push_back( test );
          }
        }
        conc = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( OR, children );
        Trace("datatypes-infer") << "DtInfer : zero size : " << conc << std::endl;
        d_pending.push_back( conc );
        d_pending_exp[ conc ] = d_true;
        d_infer.push_back( conc );
*/
      }

      if( n.getKind() == DT_HEIGHT_BOUND ){
        if( n[1].getConst<Rational>().isZero() ){
          std::vector< Node > children;
          const Datatype& dt = ((DatatypeType)(n[0].getType()).toType()).getDatatype();
          for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
            if( DatatypesRewriter::isNullaryConstructor( dt[i] ) ){
              Node test = DatatypesRewriter::mkTester( n[0], i, dt );
              children.push_back( test );
            }
          }
          Node lem;
          if( children.empty() ){
            lem = n.negate();
          }else{
            lem = NodeManager::currentNM()->mkNode( IFF, n, children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( OR, children ) );
          }
          Trace("datatypes-infer") << "DtInfer : zero height : " << lem << std::endl;
          d_pending.push_back( lem );
          d_pending_exp[ lem ] = d_true;
          d_infer.push_back( lem );
        }
      }
    }
  }
}

void TheoryDatatypes::processNewTerm( Node n ){
  Trace("dt-terms") << "Created term : " << n << std::endl;
  //see if it is rewritten to be something different
  Node rn = Rewriter::rewrite( n );
  if( rn!=n && !areEqual( rn, n ) ){
    Node eq = n.getType().isBoolean() ? rn.iffNode( n ) : rn.eqNode( n );
    d_pending.push_back( eq );
    d_pending_exp[ eq ] = d_true;
    Trace("datatypes-infer") << "DtInfer : rewrite : " << eq << std::endl;
    d_infer.push_back( eq );
  }
}

Node TheoryDatatypes::getInstantiateCons( Node n, const Datatype& dt, int index ){
  std::map< int, Node >::iterator it = d_inst_map[n].find( index );
  if( it!=d_inst_map[n].end() ){
    return it->second;
  }else{
    //add constructor to equivalence class
    Node k = n;
    if( n.getKind()==APPLY_CONSTRUCTOR ){
      //must construct variable to refer to n, add lemma immediately
      k = NodeManager::currentNM()->mkSkolem( "k", n.getType(), "for dt instantiation" );
      Node eq = k.eqNode( n );
      Trace("datatypes-infer") << "DtInfer : instantiation ref : " << eq << std::endl;
      d_out->lemma( eq );
    }
    Node n_ic = DatatypesRewriter::getInstCons( k, dt, index );
    //Assert( n_ic==Rewriter::rewrite( n_ic ) );
    n_ic = Rewriter::rewrite( n_ic );
    collectTerms( n_ic );
    d_equalityEngine.addTerm(n_ic);
    Debug("dt-enum") << "Made instantiate cons " << n_ic << std::endl;
    d_inst_map[n][index] = n_ic;
    return n_ic;
  }
}

void TheoryDatatypes::instantiate( EqcInfo* eqc, Node n ){
  //add constructor to equivalence class if not done so already
  if( hasLabel( eqc, n ) && !eqc->d_inst ){
    Node exp;
    Node tt;
    if( !eqc->d_constructor.get().isNull() ){
      exp = d_true;
      tt = eqc->d_constructor;
    }else{
      exp = getLabel( n );
      tt = exp[0];
    }
    int index = getLabelIndex( eqc, n );
    const Datatype& dt = ((DatatypeType)(tt.getType()).toType()).getDatatype();
    //must be finite or have a selector
    //if( eqc->d_selectors || dt[ index ].isFinite() ){
    //instantiate this equivalence class
    eqc->d_inst = true;
    Node tt_cons = getInstantiateCons( tt, dt, index );
    Node eq;
    if( tt!=tt_cons ){
      eq = tt.eqNode( tt_cons );
      Debug("datatypes-inst") << "DtInstantiate : " << eqc << " " << eq << std::endl;
      d_pending.push_back( eq );
      d_pending_exp[ eq ] = exp;
      Trace("datatypes-infer") << "DtInfer : instantiate : " << eq << " by " << exp << std::endl;
      //eqc->d_inst.set( eq );
      d_infer.push_back( eq );
      d_infer_exp.push_back( exp );
    }
    //}
    //else{
    //  Debug("datatypes-inst") << "Do not instantiate" << std::endl;
    //}
  }
}

void TheoryDatatypes::checkCycles() {
  Debug("datatypes-cycle-check") << "Check cycles" << std::endl;
  std::vector< Node > cdt_eqc;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode tn = eqc.getType();
    if( DatatypesRewriter::isTypeDatatype( tn ) ) {
      if( !tn.isCodatatype() ){
        if( options::dtCyclic() ){
          //do cycle checks
          std::map< TNode, bool > visited;
          std::vector< TNode > expl;
          Node cn = searchForCycle( eqc, eqc, visited, expl );
          //if we discovered a different cycle while searching this one
          if( !cn.isNull() && cn!=eqc ){
            visited.clear();
            expl.clear();
            Node prev = cn;
            cn = searchForCycle( cn, cn, visited, expl );
            Assert( prev==cn );
          }

          if( !cn.isNull() ) {
            Assert( expl.size()>0 );
            d_conflictNode = mkAnd( expl );
            Trace("dt-conflict") << "CONFLICT: Cycle conflict : " << d_conflictNode << std::endl;
            d_out->conflict( d_conflictNode );
            d_conflict = true;
            return;
          }
        }
      }else{
        //indexing
        cdt_eqc.push_back( eqc );
      }
    }
    ++eqcs_i;
  }
  //process codatatypes
  if( cdt_eqc.size()>1 && options::cdtBisimilar() ){
    printModelDebug("dt-cdt-debug");
    Trace("dt-cdt-debug") << "Process " << cdt_eqc.size() << " co-datatypes" << std::endl;
    std::vector< std::vector< Node > > part_out;
    std::vector< TNode > exp;
    std::map< Node, Node > cn;
    std::map< Node, std::map< Node, int > > dni;
    for( unsigned i=0; i<cdt_eqc.size(); i++ ){
      cn[cdt_eqc[i]] = cdt_eqc[i];
    }
    separateBisimilar( cdt_eqc, part_out, exp, cn, dni, 0, false );
    Trace("dt-cdt-debug") << "Done separate bisimilar." << std::endl;
    if( !part_out.empty() ){
      Trace("dt-cdt-debug") << "Process partition size " << part_out.size() << std::endl;
      for( unsigned i=0; i<part_out.size(); i++ ){
        std::vector< Node > part;
        part.push_back( part_out[i][0] );
        for( unsigned j=1; j<part_out[i].size(); j++ ){
          Trace("dt-cdt") << "Codatatypes : " << part_out[i][0] << " and " << part_out[i][j] << " must be equal!!" << std::endl;
          part.push_back( part_out[i][j] );
          std::vector< std::vector< Node > > tpart_out;
          exp.clear();
          cn.clear();
          cn[part_out[i][0]] = part_out[i][0];
          cn[part_out[i][j]] = part_out[i][j];
          dni.clear();
          separateBisimilar( part, tpart_out, exp, cn, dni, 0, true );
          Assert( tpart_out.size()==1 && tpart_out[0].size()==2 );
          part.pop_back();
          //merge based on explanation
          Trace("dt-cdt") << "  exp is : ";
          for( unsigned k=0; k<exp.size(); k++ ){
            Trace("dt-cdt") << exp[k] << " ";
          }
          Trace("dt-cdt") << std::endl;
          Node eq = part_out[i][0].eqNode( part_out[i][j] );
          Node eqExp = mkAnd( exp );
          d_pending.push_back( eq );
          d_pending_exp[ eq ] = eqExp;
          Trace("datatypes-infer") << "DtInfer : cdt-bisimilar : " << eq << " by " << eqExp << std::endl;
          d_infer.push_back( eq );
          d_infer_exp.push_back( eqExp );
        }
      }
    }
  }
}

//everything is in terms of representatives
void TheoryDatatypes::separateBisimilar( std::vector< Node >& part, std::vector< std::vector< Node > >& part_out,
                                         std::vector< TNode >& exp,
                                         std::map< Node, Node >& cn,
                                         std::map< Node, std::map< Node, int > >& dni, int dniLvl, bool mkExp ){
  if( !mkExp ){
    Trace("dt-cdt-debug") << "Separate bisimilar : " << std::endl;
    for( unsigned i=0; i<part.size(); i++ ){
      Trace("dt-cdt-debug") << "   " << part[i] << ", current = " << cn[part[i]] << std::endl;
    }
  }
  Assert( part.size()>1 );
  std::map< Node, std::vector< Node > > new_part;
  std::map< Node, std::vector< Node > > new_part_c;
  std::map< int, std::vector< Node > > new_part_rec;

  std::map< Node, Node > cn_cons;
  for( unsigned j=0; j<part.size(); j++ ){
    Node c = cn[part[j]];
    std::map< Node, int >::iterator it_rec = dni[part[j]].find( c );
    if( it_rec!=dni[part[j]].end() ){
      //looped
      if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is looping at index " << it_rec->second << std::endl; }
      new_part_rec[ it_rec->second ].push_back( part[j] );
    }else{
      if( DatatypesRewriter::isTermDatatype( c ) ){
        Node ncons = getEqcConstructor( c );
        if( ncons.getKind()==APPLY_CONSTRUCTOR ) {
          Node cc = ncons.getOperator();
          cn_cons[part[j]] = ncons;
          if( mkExp ){
            explainEquality( c, ncons, true, exp );
          }
          new_part[cc].push_back( part[j] );
          if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is datatype " << ncons << "." << std::endl; }
        }else{
          new_part_c[c].push_back( part[j] );
          if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is unspecified datatype." << std::endl; }
        }
      }else{
        //add equivalences
        if( !mkExp ){ Trace("dt-cdt-debug") << "  - " << part[j] << " is term " << c << "." << std::endl; }
        new_part_c[c].push_back( part[j] );
      }
    }
  }
  //direct add for constants
  for( std::map< Node, std::vector< Node > >::iterator it = new_part_c.begin(); it != new_part_c.end(); ++it ){
    if( it->second.size()>1 ){
      std::vector< Node > vec;
      vec.insert( vec.begin(), it->second.begin(), it->second.end() );
      part_out.push_back( vec );
    }
  }
  //direct add for recursive
  for( std::map< int, std::vector< Node > >::iterator it = new_part_rec.begin(); it != new_part_rec.end(); ++it ){
    if( it->second.size()>1 ){
      std::vector< Node > vec;
      vec.insert( vec.begin(), it->second.begin(), it->second.end() );
      part_out.push_back( vec );
    }else{
      //add back : could match a datatype?
    }
  }
  //recurse for the datatypes
  for( std::map< Node, std::vector< Node > >::iterator it = new_part.begin(); it != new_part.end(); ++it ){
    if( it->second.size()>1 ){
      //set dni to check for loops
      std::map< Node, Node > dni_rem;
      for( unsigned i=0; i<it->second.size(); i++ ){
        Node n = it->second[i];
        dni[n][cn[n]] = dniLvl;
        dni_rem[n] = cn[n];
      }

      //we will split based on the arguments of the datatype
      std::vector< std::vector< Node > > split_new_part;
      split_new_part.push_back( it->second );

      unsigned nChildren = cn_cons[it->second[0]].getNumChildren();
      //for each child of constructor
      unsigned cindex = 0;
      while( cindex<nChildren && !split_new_part.empty() ){
        if( !mkExp ){ Trace("dt-cdt-debug") << "Split argument #" << cindex << " of " << it->first << "..." << std::endl; }
        std::vector< std::vector< Node > > next_split_new_part;
        for( unsigned j=0; j<split_new_part.size(); j++ ){
          //set current node
          for( unsigned k=0; k<split_new_part[j].size(); k++ ){
            Node n = split_new_part[j][k];
            cn[n] = getRepresentative( cn_cons[n][cindex] );
            if( mkExp ){
              explainEquality( cn[n], cn_cons[n][cindex], true, exp );
            }
          }
          std::vector< std::vector< Node > > c_part_out;
          separateBisimilar( split_new_part[j], c_part_out, exp, cn, dni, dniLvl+1, mkExp );
          next_split_new_part.insert( next_split_new_part.end(), c_part_out.begin(), c_part_out.end() );
        }
        split_new_part.clear();
        split_new_part.insert( split_new_part.end(), next_split_new_part.begin(), next_split_new_part.end() );
        cindex++;
      }
      part_out.insert( part_out.end(), split_new_part.begin(), split_new_part.end() );

      for( std::map< Node, Node >::iterator it2 = dni_rem.begin(); it2 != dni_rem.end(); ++it2 ){
        dni[it2->first].erase( it2->second );
      }
    }
  }
}

//postcondition: if cycle detected, explanation is why n is a subterm of on
Node TheoryDatatypes::searchForCycle( TNode n, TNode on,
                                      std::map< TNode, bool >& visited,
                                      std::vector< TNode >& explanation, bool firstTime ) {
  Debug("datatypes-cycle-check") << "Search for cycle " << n << " " << on << endl;
  TNode ncons;
  TNode nn;
  if( !firstTime ){
    nn = getRepresentative( n );
    if( nn==on ){
      explainEquality( n, nn, true, explanation );
      return on;
    }
  }else{
    nn = n;
  }
  if( visited.find( nn ) == visited.end() ) {
    visited[nn] = true;
    TNode ncons = getEqcConstructor( nn );
    if( ncons.getKind()==APPLY_CONSTRUCTOR ) {
      for( int i=0; i<(int)ncons.getNumChildren(); i++ ) {
        TNode cn = searchForCycle( ncons[i], on, visited, explanation, false );
        if( cn==on ) {
          //if( Debug.isOn("datatypes-cycles") && !d_cycle_check.isConnectedNode( n, ncons[i] ) ){
          //  Debug("datatypes-cycles") << "Cycle subterm: " << n << " is not -> " << ncons[i] << "!!!!" << std::endl;
          //}
          //add explanation for why the constructor is connected
          if( n != ncons ) {
            explainEquality( n, ncons, true, explanation );
          }
          return on;
        }else if( !cn.isNull() ){
          return cn;
        }
      }
    }
    visited.erase( nn );
    return Node::null();
  }else{
    TypeNode tn = nn.getType();
    if( DatatypesRewriter::isTypeDatatype( tn ) ) {
      if( !tn.isCodatatype() ){
        return nn;
      }
    }
    return Node::null();
  }
}

bool TheoryDatatypes::mustCommunicateFact( Node n, Node exp ){
  //the datatypes decision procedure makes "internal" inferences apart from the equality engine :
  //  (1) Unification : C( t1...tn ) = C( s1...sn ) => ti = si
  //  (2) Label : ~is_C1( t ) ... ~is_C{i-1}( t ) ~is_C{i+1}( t ) ... ~is_Cn( t ) => is_Ci( t )
  //  (3) Instantiate : is_C( t ) => t = C( sel_1( t ) ... sel_n( t ) )
  //  (4) collapse selector : S( C( t1...tn ) ) = t'
  //  (5) collapse term size : size( C( t1...tn ) ) = 1 + size( t1 ) + ... + size( tn )
  //  (6) non-negative size : 0 <= size( t )
  //We may need to communicate outwards if the conclusions involve other theories.  Also communicate (6) and OR conclusions.
  Trace("dt-lemma-debug") << "Compute for " << exp << " => " << n << std::endl;
  bool addLemma = false;
  if( n.getKind()==EQUAL || n.getKind()==IFF ){
    /*
    for( unsigned i=0; i<2; i++ ){
      if( !n[i].isVar() && n[i].getKind()!=APPLY_SELECTOR_TOTAL && n[i].getKind()!=APPLY_CONSTRUCTOR ){
        addLemma = true;
      }
    }
    */
    TypeNode tn = n[0].getType();
    if( !DatatypesRewriter::isTypeDatatype( tn ) ){
      addLemma = true;
    }else{
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      addLemma = dt.involvesExternalType();
    }
    //for( int j=0; j<(int)n[1].getNumChildren(); j++ ){
    //  if( !DatatypesRewriter::isTermDatatype( n[1][j] ) ){
    //    addLemma = true;
    //    break;
    //  }
    //}
  }else if( n.getKind()==LEQ ){
    addLemma = true;
  }else if( n.getKind()==OR ){
    addLemma = true;
  }
  if( addLemma ){
    //check if we have already added this lemma
    //if( std::find( d_inst_lemmas[ n[0] ].begin(), d_inst_lemmas[ n[0] ].end(), n[1] )==d_inst_lemmas[ n[0] ].end() ){
    //  d_inst_lemmas[ n[0] ].push_back( n[1] );
    Trace("dt-lemma-debug") << "Communicate " << n << std::endl;
    return true;
    //}else{
    //  Trace("dt-lemma-debug") << "Already communicated " << n << std::endl;
    //  return false;
    //}
  }
  //else if( exp.getKind()==APPLY_TESTER ){
    //if( n.getKind()==EQUAL && !DatatypesRewriter::isTermDatatype( n[0] ) ){
    //  return true;
    //}
  //}
  Trace("dt-lemma-debug") << "Do not need to communicate " << n << std::endl;
  return false;
}

bool TheoryDatatypes::hasTerm( TNode a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheoryDatatypes::areEqual( TNode a, TNode b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryDatatypes::areDisequal( TNode a, TNode b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

TNode TheoryDatatypes::getRepresentative( TNode a ){
  if( hasTerm( a ) ){
    return d_equalityEngine.getRepresentative( a );
  }else{
    return a;
  }
}


void TheoryDatatypes::printModelDebug( const char* c ){
  if(! (Trace.isOn(c))) {
    return;
  }

  Trace( c ) << "Datatypes model : " << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    if( !eqc.getType().isBoolean() ){
      if( DatatypesRewriter::isTermDatatype( eqc ) ){
        Trace( c ) << "DATATYPE : ";
      }
      Trace( c ) << eqc << " : " << eqc.getType() << " : " << std::endl;
      Trace( c ) << "   { ";
      //add terms to model
      eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
      while( !eqc_i.isFinished() ){
        if( (*eqc_i)!=eqc ){
          Trace( c ) << (*eqc_i) << " ";
        }
        ++eqc_i;
      }
      Trace( c ) << "}" << std::endl;
      if( DatatypesRewriter::isTermDatatype( eqc ) ){
        EqcInfo* ei = getOrMakeEqcInfo( eqc );
        if( ei ){
          Trace( c ) << "   Instantiated : " << ei->d_inst.get() << std::endl;
          Trace( c ) << "   Constructor : ";
          if( !ei->d_constructor.get().isNull() ){
            Trace( c )<< ei->d_constructor.get();
          }
          Trace( c ) << std::endl << "   Labels : ";
          if( hasLabel( ei, eqc ) ){
            Trace( c ) << getLabel( eqc );
          }else{
            NodeListMap::iterator lbl_i = d_labels.find( eqc );
            if( lbl_i != d_labels.end() ){
              NodeList* lbl = (*lbl_i).second;
              for( NodeList::const_iterator j = lbl->begin(); j != lbl->end(); j++ ){
                Trace( c ) << *j << " ";
              }
            }
          }
          Trace( c ) << std::endl;
          Trace( c ) << "   Selectors : " << ( ei->d_selectors ? "yes, " : "no " );
          NodeListMap::iterator sel_i = d_selector_apps.find( eqc );
          if( sel_i != d_selector_apps.end() ){
            NodeList* sel = (*sel_i).second;
            for( NodeList::const_iterator j = sel->begin(); j != sel->end(); j++ ){
              Trace( c ) << *j << " ";
            }
          }
          Trace( c ) << std::endl;
        }
      }
    }
    ++eqcs_i;
  }
}

Node TheoryDatatypes::mkAnd( std::vector< TNode >& assumptions ) {
  if( assumptions.empty() ){
    return d_true;
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( AND, assumptions );
  }
}

bool TheoryDatatypes::checkClashModEq( TNode n1, TNode n2, std::vector< Node >& exp, std::vector< std::pair< TNode, TNode > >& deq_cand ) {
  if( (n1.getKind() == kind::APPLY_CONSTRUCTOR && n2.getKind() == kind::APPLY_CONSTRUCTOR) ||
      (n1.getKind() == kind::TUPLE && n2.getKind() == kind::TUPLE) ||
      (n1.getKind() == kind::RECORD && n2.getKind() == kind::RECORD) ) {
    if( n1.getOperator() != n2.getOperator() ) {
      return true;
    } else {
      Assert( n1.getNumChildren() == n2.getNumChildren() );
      for( int i=0; i<(int)n1.getNumChildren(); i++ ) {
        TNode nc1 = getEqcConstructor( n1[i] );
        TNode nc2 = getEqcConstructor( n2[i] );
        if( checkClashModEq( nc1, nc2, exp, deq_cand ) ) {
          if( nc1!=n1[i] ){
            exp.push_back( nc1.eqNode( n1[i] ) );
          }
          if( nc2!=n2[i] ){
            exp.push_back( nc2.eqNode( n2[i] ) );
          }
          return true;
        }
      }
    }
  }else if( n1!=n2 ){
    if( n1.isConst() && n2.isConst() ){
      return true;
    }else{
      if( !areEqual( n1, n2 ) ){
        deq_cand.push_back( std::pair< TNode, TNode >( n1, n2 ) );
      }
    }
  }
  return false;
}
