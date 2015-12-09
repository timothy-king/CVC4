/*********************                                                        */
/*! \file inst_strategy_e_matching.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of e matching instantiation strategies
 **/

#include "options/quantifiers_options.h"
#include "theory/quantifiers/inst_match_generator.h"
#include "theory/quantifiers/inst_strategy_e_matching.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;
using namespace CVC4::theory::quantifiers;

//priority levels :
//1 : user patterns (when user-pat!={resort,ignore}), auto-gen patterns (for non-user pattern quantifiers, or when user-pat={resort,ignore})
//2 : user patterns (when user-pat=resort), auto gen patterns (for user pattern quantifiers when user-pat=use)

// user-pat=interleave alternates between use and resort

struct sortQuantifiersForSymbol {
  QuantifiersEngine* d_qe;
  bool operator() (Node i, Node j) {
    int nqfsi = d_qe->getQuantifierRelevance()->getNumQuantifiersForSymbol( i.getOperator() );
    int nqfsj = d_qe->getQuantifierRelevance()->getNumQuantifiersForSymbol( j.getOperator() );
    if( nqfsi<nqfsj ){
      return true;
    }else if( nqfsi>nqfsj ){
      return false;
    }else{
      return false;
    }
  }
};

struct sortTriggers {
  bool operator() (Node i, Node j) {
    if( Trigger::isAtomicTrigger( i ) ){
      return i<j || !Trigger::isAtomicTrigger( j );
    }else{
      return i<j && !Trigger::isAtomicTrigger( j );
    }
  }
};

void InstStrategyUserPatterns::processResetInstantiationRound( Theory::Effort effort ){
  //reset triggers
  for( std::map< Node, std::vector< Trigger* > >::iterator it = d_user_gen.begin(); it != d_user_gen.end(); ++it ){
    for( unsigned i=0; i<it->second.size(); i++ ){
      it->second[i]->resetInstantiationRound();
      it->second[i]->reset( Node::null() );
    }
  }
}

int InstStrategyUserPatterns::process( Node f, Theory::Effort effort, int e ){
  if( e==0 ){
    return STATUS_UNFINISHED;
  }else{
    int peffort = d_quantEngine->getInstUserPatMode()==USER_PAT_MODE_RESORT ? 2 : 1;
    if( e<peffort ){
      return STATUS_UNFINISHED;
    }else if( e==peffort ){
      d_counter[f]++;

      Trace("inst-alg") << "-> User-provided instantiate " << f << "..." << std::endl;
      if( d_quantEngine->getInstUserPatMode()==USER_PAT_MODE_RESORT  ){
        int matchOption = 0;
        for( unsigned i=0; i<d_user_gen_wait[f].size(); i++ ){
          Trigger * t = Trigger::mkTrigger( d_quantEngine, f, d_user_gen_wait[f][i], matchOption, true, Trigger::TR_RETURN_NULL, options::smartTriggers() );
          if( t ){
            d_user_gen[f].push_back( t );
          }
        }
        d_user_gen_wait[f].clear();
      }

      for( unsigned i=0; i<d_user_gen[f].size(); i++ ){
        bool processTrigger = true;
        if( processTrigger ){
          Trace("process-trigger") << "  Process (user) ";
          d_user_gen[f][i]->debugPrint("process-trigger");
          Trace("process-trigger") << "..." << std::endl;
          InstMatch baseMatch( f );
          int numInst = d_user_gen[f][i]->addInstantiations( baseMatch );
          Trace("process-trigger") << "  Done, numInst = " << numInst << "." << std::endl;
          d_quantEngine->d_statistics.d_instantiations_user_patterns += numInst;
          if( d_user_gen[f][i]->isMultiTrigger() ){
            d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
          }
          //d_quantEngine->d_hasInstantiated[f] = true;
        }
      }
    }
  }
  return STATUS_UNKNOWN;
}

void InstStrategyUserPatterns::addUserPattern( Node q, Node pat ){
  Assert( pat.getKind()==INST_PATTERN );
  //add to generators
  bool usable = true;
  std::vector< Node > nodes;
  for( unsigned i=0; i<pat.getNumChildren(); i++ ){
    nodes.push_back( pat[i] );
    if( pat[i].getKind()!=INST_CONSTANT && !Trigger::isUsableTrigger( pat[i], q ) ){
      Trace("trigger-warn") << "User-provided trigger is not usable : " << pat << " because of " << pat[i] << std::endl;
      usable = false;
      break;
    }
  }
  if( usable ){
    Trace("user-pat") << "Add user pattern: " << pat << " for " << q << std::endl;
    //check match option
    int matchOption = 0;
    if( d_quantEngine->getInstUserPatMode()==USER_PAT_MODE_RESORT ){
      d_user_gen_wait[q].push_back( nodes );
    }else{
      d_user_gen[q].push_back( Trigger::mkTrigger( d_quantEngine, q, nodes, matchOption, true, Trigger::TR_MAKE_NEW, options::smartTriggers() ) );
    }
  }
}

InstStrategyAutoGenTriggers::InstStrategyAutoGenTriggers( QuantifiersEngine* qe ) : InstStrategy( qe ){
  //how to select trigger terms
  if( options::triggerSelMode()==TRIGGER_SEL_MIN ){
    d_tr_strategy = Trigger::TS_MIN_TRIGGER;
  }else if( options::triggerSelMode()==TRIGGER_SEL_MAX ){
    d_tr_strategy = Trigger::TS_MAX_TRIGGER;
  }else{
    d_tr_strategy = Trigger::TS_ALL;
  }
  //whether to select new triggers during the search
  if( options::incrementTriggers() ){
    d_regenerate_frequency = 3;
    d_regenerate = true;
  }else{
    d_regenerate = false;
  }
}

void InstStrategyAutoGenTriggers::processResetInstantiationRound( Theory::Effort effort ){
  //reset triggers
  for( unsigned r=0; r<2; r++ ){
    for( std::map< Node, std::map< Trigger*, bool > >::iterator it = d_auto_gen_trigger[r].begin(); it != d_auto_gen_trigger[r].end(); ++it ){
      for( std::map< Trigger*, bool >::iterator itt = it->second.begin(); itt != it->second.end(); ++itt ){
        itt->first->resetInstantiationRound();
        itt->first->reset( Node::null() );
      }
    }
  }
  d_processed_trigger.clear();
}

int InstStrategyAutoGenTriggers::process( Node f, Theory::Effort effort, int e ){
  UserPatMode upMode = d_quantEngine->getInstUserPatMode();
  if( hasUserPatterns( f ) && upMode==USER_PAT_MODE_TRUST ){
    return STATUS_UNKNOWN;
  }else{
    int peffort = ( hasUserPatterns( f ) && upMode!=USER_PAT_MODE_IGNORE && upMode!=USER_PAT_MODE_RESORT ) ? 2 : 1;
    if( e<peffort ){
      return STATUS_UNFINISHED;
    }else{
      Trace("inst-alg") << "-> Auto-gen instantiate " << f << "..." << std::endl;
      bool gen = false;
      if( e==peffort ){
        if( d_counter.find( f )==d_counter.end() ){
          d_counter[f] = 0;
          gen = true;
        }else{
          d_counter[f]++;
          gen = d_regenerate && d_counter[f]%d_regenerate_frequency==0;
        }
      }else{
        gen = true;
      }
      if( gen ){
        generateTriggers( f );
        if( d_counter[f]==0 && d_auto_gen_trigger[0][f].empty() && d_auto_gen_trigger[1][f].empty() && f.getNumChildren()==2 ){
          Trace("trigger-warn") << "Could not find trigger for " << f << std::endl;
        }
      }

      //if( e==4 ){
      //  d_processed_trigger.clear();
      //  d_quantEngine->getEqualityQuery()->setLiberal( true );
      //}
      bool hasInst = false;
      for( unsigned r=0; r<2; r++ ){
        for( std::map< Trigger*, bool >::iterator itt = d_auto_gen_trigger[r][f].begin(); itt != d_auto_gen_trigger[r][f].end(); ++itt ){
          Trigger* tr = itt->first;
          if( tr ){
            bool processTrigger = itt->second;
            if( processTrigger && d_processed_trigger[f].find( tr )==d_processed_trigger[f].end() ){
              d_processed_trigger[f][tr] = true;
              Trace("process-trigger") << "  Process ";
              tr->debugPrint("process-trigger");
              Trace("process-trigger") << "..." << std::endl;
              InstMatch baseMatch( f );
              int numInst = tr->addInstantiations( baseMatch );
              hasInst = numInst>0 || hasInst;
              Trace("process-trigger") << "  Done, numInst = " << numInst << "." << std::endl;
              d_quantEngine->d_statistics.d_instantiations_auto_gen += numInst;
              if( r==1 ){
                d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
              }
              //d_quantEngine->d_hasInstantiated[f] = true;
            }
          }
        }
        if( hasInst && options::multiTriggerPriority() ){
          break;
        }
      }
      //if( e==4 ){
      //  d_quantEngine->getEqualityQuery()->setLiberal( false );
      //}
      return STATUS_UNKNOWN;
    }
  }
}

void InstStrategyAutoGenTriggers::generateTriggers( Node f ){
  Trace("auto-gen-trigger-debug") << "Generate triggers for " << f << std::endl;
  if( d_patTerms[0].find( f )==d_patTerms[0].end() ){
    //determine all possible pattern terms based on trigger term selection strategy d_tr_strategy
    d_patTerms[0][f].clear();
    d_patTerms[1][f].clear();
    bool ntrivTriggers = options::relationalTriggers();
    std::vector< Node > patTermsF;
    //well-defined function: can assume LHS is only trigger
    if( options::quantFunWellDefined() ){
      Node hd = TermDb::getFunDefHead( f );
      if( !hd.isNull() ){
        hd = d_quantEngine->getTermDatabase()->getInstConstantNode( hd, f );
        patTermsF.push_back( hd );
      }
    }
    //otherwise, use algorithm for collecting pattern terms
    if( patTermsF.empty() ){
      Node bd = d_quantEngine->getTermDatabase()->getInstConstantBody( f );
      Trigger::collectPatTerms( d_quantEngine, f, bd, patTermsF, d_tr_strategy, d_user_no_gen[f], true );
      Trace("auto-gen-trigger-debug") << "Collected pat terms for " << bd << ", no-patterns : " << d_user_no_gen[f].size() << std::endl;
      Trace("auto-gen-trigger-debug") << "   ";
      for( int i=0; i<(int)patTermsF.size(); i++ ){
        Trace("auto-gen-trigger-debug") << patTermsF[i] << " ";
      }
      Trace("auto-gen-trigger-debug") << std::endl;
      if( ntrivTriggers ){
        sortTriggers st;
        std::sort( patTermsF.begin(), patTermsF.end(), st );
      }
    }
    //sort into single/multi triggers
    std::map< Node, std::vector< Node > > varContains;
    std::map< Node, bool > vcMap;
    std::map< Node, bool > rmPatTermsF;
    for( unsigned i=0; i<patTermsF.size(); i++ ){
      d_quantEngine->getTermDatabase()->getVarContainsNode( f, patTermsF[i], varContains[ patTermsF[i] ] );
      bool newVar = false;
      for( unsigned j=0; j<varContains[ patTermsF[i] ].size(); j++ ){
        if( vcMap.find( varContains[ patTermsF[i] ][j] )==vcMap.end() ){
          vcMap[varContains[ patTermsF[i] ][j]] = true;
          newVar = true;
        }
      }
      if( ntrivTriggers && !newVar && !Trigger::isAtomicTrigger( patTermsF[i] ) ){
        Trace("auto-gen-trigger-debug") << "Exclude expendible non-trivial trigger : " << patTermsF[i] << std::endl;
        rmPatTermsF[patTermsF[i]] = true;
      }
    }
    for( std::map< Node, std::vector< Node > >::iterator it = varContains.begin(); it != varContains.end(); ++it ){
      if( rmPatTermsF.find( it->first )==rmPatTermsF.end() ){
        if( it->second.size()==f[0].getNumChildren() && ( options::pureThTriggers() || !Trigger::isPureTheoryTrigger( it->first ) ) ){
          d_patTerms[0][f].push_back( it->first );
          d_is_single_trigger[ it->first ] = true;
        }else{
          d_patTerms[1][f].push_back( it->first );
          d_is_single_trigger[ it->first ] = false;
        }
      }
    }
    d_made_multi_trigger[f] = false;
    Trace("auto-gen-trigger") << "Single triggers for " << f << " : " << std::endl;
    for( unsigned i=0; i<d_patTerms[0][f].size(); i++ ){
      Trace("auto-gen-trigger") << "   " << d_patTerms[0][f][i] << std::endl;
    }
    if( !d_patTerms[1][f].empty() ){
      Trace("auto-gen-trigger") << "Multi-trigger term pool for " << f << " : " << std::endl;
      for( unsigned i=0; i<d_patTerms[1][f].size(); i++ ){
        Trace("auto-gen-trigger") << "   " << d_patTerms[1][f][i] << std::endl;
      }
    }
  }

  unsigned rmin = d_patTerms[0][f].empty() ? 1 : 0;
  unsigned rmax = options::multiTriggerWhenSingle() ? 1 : rmin;
  for( unsigned r=rmin; r<=rmax; r++ ){
    std::vector< Node > patTerms;
    for( int i=0; i<(int)d_patTerms[r][f].size(); i++ ){
      if( r==1 || d_single_trigger_gen.find( d_patTerms[r][f][i] )==d_single_trigger_gen.end() ){
        patTerms.push_back( d_patTerms[r][f][i] );
      }
    }
    if( !patTerms.empty() ){
      Trace("auto-gen-trigger") << "Generate trigger for " << f << std::endl;
      //sort terms based on relevance
      if( options::relevantTriggers() ){
        sortQuantifiersForSymbol sqfs;
        sqfs.d_qe = d_quantEngine;
        //sort based on # occurrences (this will cause Trigger to select rarer symbols)
        std::sort( patTerms.begin(), patTerms.end(), sqfs );
        Debug("relevant-trigger") << "Terms based on relevance: " << std::endl;
        for( int i=0; i<(int)patTerms.size(); i++ ){
          Debug("relevant-trigger") << "   " << patTerms[i] << " (";
          Debug("relevant-trigger") << d_quantEngine->getQuantifierRelevance()->getNumQuantifiersForSymbol( patTerms[i].getOperator() ) << ")" << std::endl;
        }
      }
      //now, generate the trigger...
      int matchOption = 0;
      Trigger* tr = NULL;
      if( d_is_single_trigger[ patTerms[0] ] ){
        tr = Trigger::mkTrigger( d_quantEngine, f, patTerms[0], matchOption, false, Trigger::TR_RETURN_NULL, options::smartTriggers() );
        d_single_trigger_gen[ patTerms[0] ] = true;
      }else{
        //only generate multi trigger if option set, or if no single triggers exist
        if( !d_patTerms[0][f].empty() ){
          if( options::multiTriggerWhenSingle() ){
            Trace("multi-trigger-debug") << "Resort to choosing multi-triggers..." << std::endl;
          }else{
            return;
          }
        }
        //if we are re-generating triggers, shuffle based on some method
        if( d_made_multi_trigger[f] ){
          std::random_shuffle( patTerms.begin(), patTerms.end() ); //shuffle randomly
        }else{
          d_made_multi_trigger[f] = true;
        }
        //will possibly want to get an old trigger
        tr = Trigger::mkTrigger( d_quantEngine, f, patTerms, matchOption, false, Trigger::TR_GET_OLD, options::smartTriggers() );
      }
      if( tr ){
        unsigned tindex;
        if( tr->isMultiTrigger() ){
          //disable all other multi triggers
          for( std::map< Trigger*, bool >::iterator it = d_auto_gen_trigger[1][f].begin(); it != d_auto_gen_trigger[1][f].end(); ++it ){
            d_auto_gen_trigger[1][f][ it->first ] = false;
          }
          tindex = 1;
        }else{
          tindex = 0;
        }
        //making it during an instantiation round, so must reset
        if( d_auto_gen_trigger[tindex][f].find( tr )==d_auto_gen_trigger[tindex][f].end() ){
          tr->resetInstantiationRound();
          tr->reset( Node::null() );
        }
        d_auto_gen_trigger[tindex][f][tr] = true;
        //if we are generating additional triggers...
        if( tindex==0 ){
          int index = 0;
          if( index<(int)patTerms.size() ){
            //Notice() << "check add additional" << std::endl;
            //check if similar patterns exist, and if so, add them additionally
            int nqfs_curr = 0;
            if( options::relevantTriggers() ){
              nqfs_curr = d_quantEngine->getQuantifierRelevance()->getNumQuantifiersForSymbol( patTerms[0].getOperator() );
            }
            index++;
            bool success = true;
            while( success && index<(int)patTerms.size() && d_is_single_trigger[ patTerms[index] ] ){
              success = false;
              if( !options::relevantTriggers() ||
                  d_quantEngine->getQuantifierRelevance()->getNumQuantifiersForSymbol( patTerms[index].getOperator() )<=nqfs_curr ){
                d_single_trigger_gen[ patTerms[index] ] = true;
                Trigger* tr2 = Trigger::mkTrigger( d_quantEngine, f, patTerms[index], matchOption, false, Trigger::TR_RETURN_NULL, options::smartTriggers() );
                if( tr2 ){
                  //Notice() << "Add additional trigger " << patTerms[index] << std::endl;
                  tr2->resetInstantiationRound();
                  tr2->reset( Node::null() );
                  d_auto_gen_trigger[0][f][tr2] = true;
                }
                success = true;
              }
              index++;
            }
            //Notice() << "done check add additional" << std::endl;
          }
        }
      }
    }
  }
}

bool InstStrategyAutoGenTriggers::hasUserPatterns( Node q ) {
  if( q.getNumChildren()==3 ){
    std::map< Node, bool >::iterator it = d_hasUserPatterns.find( q );
    if( it==d_hasUserPatterns.end() ){
      bool hasPat = false;
      for( unsigned i=0; i<q[2].getNumChildren(); i++ ){
        if( q[2][i].getKind()==INST_PATTERN ){
          hasPat = true;
          break;
        }
      }
      d_hasUserPatterns[q] = hasPat;
      return hasPat;
    }else{
      return it->second;
    }
  }else{
    return false;
  }
}

void InstStrategyAutoGenTriggers::addUserNoPattern( Node q, Node pat ) {
  Assert( pat.getKind()==INST_NO_PATTERN && pat.getNumChildren()==1 );
  if( std::find( d_user_no_gen[q].begin(), d_user_no_gen[q].end(), pat[0] )==d_user_no_gen[q].end() ){
    Trace("user-pat") << "Add user no-pattern: " << pat[0] << " for " << q << std::endl;
    d_user_no_gen[q].push_back( pat[0] );
  }
}

/*  TODO?
bool InstStrategyLocalTheoryExt::isLocalTheoryExt( Node f ) {
  std::map< Node, bool >::iterator itq = d_quant.find( f );
  if( itq==d_quant.end() ){
    //generate triggers
    Node bd = d_quantEngine->getTermDatabase()->getInstConstantBody( f );
    std::vector< Node > vars;
    std::vector< Node > patTerms;
    bool ret = Trigger::isLocalTheoryExt( bd, vars, patTerms );
    if( ret ){
      d_quant[f] = ret;
      //add all variables to trigger that don't already occur
      for( unsigned i=0; i<f[0].getNumChildren(); i++ ){
        Node x = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
        if( std::find( vars.begin(), vars.end(), x )==vars.end() ){
          patTerms.push_back( x );
        }
      }
      Trace("local-t-ext") << "Local theory extensions trigger for " << f << " : " << std::endl;
      for( unsigned i=0; i<patTerms.size(); i++ ){
        Trace("local-t-ext") << "  " << patTerms[i] << std::endl;
      }
      Trace("local-t-ext") << std::endl;
      int matchOption = 0;
      Trigger * tr = Trigger::mkTrigger( d_quantEngine, f, patTerms, matchOption, true, Trigger::TR_GET_OLD, options::smartTriggers() );
      d_lte_trigger[f] = tr;
    }else{
      Trace("local-t-ext") << "No local theory extensions trigger for " << f << "." << std::endl;
      Trace("local-t-ext-warn") << "WARNING: not local theory extensions : " << f << std::endl;
    }
    d_quant[f] = ret;
    return ret;
  }else{
    return itq->second;
  }
}
*/
FullSaturation::FullSaturation( QuantifiersEngine* qe ) : QuantifiersModule( qe ){

}

bool FullSaturation::needsCheck( Theory::Effort e ){
  if( options::fullSaturateInst() ){
    if( d_quantEngine->getInstWhenNeedsCheck( e ) ){
      return true;
    }
  }
  if( options::fullSaturateQuant() ){
    if( e>=Theory::EFFORT_LAST_CALL ){
      return true;
    }
  }
  return false;
}

void FullSaturation::reset_round( Theory::Effort e ) {

}

void FullSaturation::check( Theory::Effort e, unsigned quant_e ) {
  bool doCheck = false;
  bool fullEffort = false;
  if( options::fullSaturateInst() ){
    //we only add when interleaved with other strategies
    doCheck = quant_e==QuantifiersEngine::QEFFORT_STANDARD && d_quantEngine->hasAddedLemma();
  }
  if( options::fullSaturateQuant() && !doCheck ){
    doCheck = quant_e==QuantifiersEngine::QEFFORT_LAST_CALL;
    fullEffort = !d_quantEngine->hasAddedLemma();
  }
  if( doCheck ){
    double clSet = 0;
    if( Trace.isOn("fs-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("fs-engine") << "---Full Saturation Round, effort = " << e << "---" << std::endl;
    }
    int addedLemmas = 0;
    for( int i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( d_quantEngine->hasOwnership( q, this ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
        if( process( q, fullEffort ) ){
          //added lemma
          addedLemmas++;
        }
      }
    }
    if( Trace.isOn("fs-engine") ){
      Trace("fs-engine") << "Added lemmas = " << addedLemmas  << std::endl;
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("fs-engine") << "Finished instantiation engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

bool FullSaturation::process( Node f, bool fullEffort ){
  //first, try from relevant domain
  RelevantDomain * rd = d_quantEngine->getRelevantDomain();
  unsigned rstart = options::fullSaturateQuantRd() ? 0 : 1;
  unsigned rend = fullEffort ? 1 : rstart;
  for( unsigned r=rstart; r<=rend; r++ ){
      /*
      //complete guess
      if( d_guessed.find( f )==d_guessed.end() ){
        Trace("inst-alg") << "-> Guess instantiate " << f << "..." << std::endl;
        d_guessed[f] = true;
        InstMatch m( f );
        if( d_quantEngine->addInstantiation( f, m ) ){
          ++(d_quantEngine->d_statistics.d_instantiations_guess);
          return true;
        }
      }
      */
    if( rd || r>0 ){
      if( r==0 ){
        Trace("inst-alg") << "-> Relevant domain instantiate " << f << "..." << std::endl;
      }else{
        Trace("inst-alg") << "-> Ground term instantiate " << f << "..." << std::endl;
      }
      rd->compute();
      unsigned final_max_i = 0;
      std::vector< unsigned > maxs;
      std::vector< bool > max_zero;
      bool has_zero = false;
      for(unsigned i=0; i<f[0].getNumChildren(); i++ ){
        unsigned ts;
        if( r==0 ){
          ts = rd->getRDomain( f, i )->d_terms.size();
        }else{
          ts = d_quantEngine->getTermDatabase()->d_type_map[f[0][i].getType()].size();
        }
        max_zero.push_back( fullEffort && ts==0 );
        ts = ( fullEffort && ts==0 ) ? 1 : ts;
        Trace("inst-alg-rd") << "Variable " << i << " has " << ts << " in relevant domain." << std::endl;
        if( ts==0 ){
          has_zero = true;
          break;
        }else{
          maxs.push_back( ts );
          if( ts>final_max_i ){
            final_max_i = ts;
          }
        }
      }
      if( !has_zero ){
        Trace("inst-alg-rd") << "Will do " << final_max_i << " stages of instantiation." << std::endl;
        unsigned max_i = 0;
        bool success;
        while( max_i<=final_max_i ){
          Trace("inst-alg-rd") << "Try stage " << max_i << "..." << std::endl;
          std::vector< unsigned > childIndex;
          int index = 0;
          do {
            while( index>=0 && index<(int)f[0].getNumChildren() ){
              if( index==(int)childIndex.size() ){
                childIndex.push_back( -1 );
              }else{
                Assert( index==(int)(childIndex.size())-1 );
                unsigned nv = childIndex[index]+1;
                if( options::cbqi() && r==1 && !max_zero[index] ){
                  //skip inst constant nodes
                  while( nv<maxs[index] && nv<=max_i &&
                          quantifiers::TermDb::hasInstConstAttr( d_quantEngine->getTermDatabase()->d_type_map[f[0][index].getType()][nv] ) ){
                    nv++;
                  }
                }
                if( nv<maxs[index] && nv<=max_i ){
                  childIndex[index] = nv;
                  index++;
                }else{
                  childIndex.pop_back();
                  index--;
                }
              }
            }
            success = index>=0;
            if( success ){
              Trace("inst-alg-rd") << "Try instantiation { ";
              for( unsigned j=0; j<childIndex.size(); j++ ){
                Trace("inst-alg-rd") << childIndex[j] << " ";
              }
              Trace("inst-alg-rd") << "}" << std::endl;
              //try instantiation
              std::vector< Node > terms;
              for( unsigned i=0; i<f[0].getNumChildren(); i++ ){
                if( max_zero[i] ){
                  //no terms available, will report incomplete instantiation
                  terms.push_back( Node::null() );
                }else if( r==0 ){
                  terms.push_back( rd->getRDomain( f, i )->d_terms[childIndex[i]] );
                }else{
                  terms.push_back( d_quantEngine->getTermDatabase()->d_type_map[f[0][i].getType()][childIndex[i]] );
                }
              }
              if( d_quantEngine->addInstantiation( f, terms, false ) ){
                Trace("inst-alg-rd") << "Success!" << std::endl;
                ++(d_quantEngine->d_statistics.d_instantiations_guess);
                return true;
              }else{
                index--;
              }
            }
          }while( success );
          max_i++;
        }
      }
    }
  }
  //term enumerator?
  return false;
}

void FullSaturation::registerQuantifier( Node q ) {

}
