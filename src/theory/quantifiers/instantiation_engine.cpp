/*********************                                                        */
/*! \file instantiation_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of instantiation engine class
 **/

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/inst_strategy_e_matching.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/trigger.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::inst;

InstantiationEngine::InstantiationEngine( QuantifiersEngine* qe ) :
QuantifiersModule( qe ){
  if( options::eMatching() ){
    //these are the instantiation strategies for E-matching
    //user-provided patterns
    if( options::userPatternsQuant()!=USER_PAT_MODE_IGNORE ){
      d_isup = new InstStrategyUserPatterns( d_quantEngine );
      d_instStrategies.push_back( d_isup );
    }

    //auto-generated patterns
    d_i_ag = new InstStrategyAutoGenTriggers( d_quantEngine );
    d_instStrategies.push_back( d_i_ag );
  }else{
    d_isup = NULL;
    d_i_ag = NULL;
  }
}

InstantiationEngine::~InstantiationEngine() {
  delete d_i_ag;
  delete d_isup;
}


void InstantiationEngine::presolve() {
  for( unsigned i=0; i<d_instStrategies.size(); ++i ){
    d_instStrategies[i]->presolve();
  }
}

bool InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  unsigned lastWaiting = d_quantEngine->getNumLemmasWaiting();
  //iterate over an internal effort level e
  int e = 0;
  int eLimit = effort==Theory::EFFORT_LAST_CALL ? 10 : 2;
  bool finished = false;
  //while unfinished, try effort level=0,1,2....
  while( !finished && e<=eLimit ){
    Debug("inst-engine") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    finished = true;
    //instantiate each quantifier
    for( unsigned i=0; i<d_quants.size(); i++ ){
      Node q = d_quants[i];
      Debug("inst-engine-debug") << "IE: Instantiate " << q << "..." << std::endl;
      //int e_use = d_quantEngine->getRelevance( q )==-1 ? e - 1 : e;
      int e_use = e;
      if( e_use>=0 ){
        Trace("inst-engine-debug") << "inst-engine : " << q << std::endl;
        //check each instantiation strategy
        for( unsigned j=0; j<d_instStrategies.size(); j++ ){
          InstStrategy* is = d_instStrategies[j];
          Trace("inst-engine-debug") << "Do " << is->identify() << " " << e_use << std::endl;
          int quantStatus = is->process( q, effort, e_use );
          Trace("inst-engine-debug") << " -> status is " << quantStatus << std::endl;
          if( quantStatus==InstStrategy::STATUS_UNFINISHED ){
            finished = false;
          }
        }
      }
    }
    //do not consider another level if already added lemma at this level
    if( d_quantEngine->getNumLemmasWaiting()>lastWaiting ){
      finished = true;
    }
    e++;
  }
  //Notice() << "All instantiators finished, # added lemmas = " << (int)d_lemmas_waiting.size() << std::endl;
  if( !d_quantEngine->hasAddedLemma() ){
    return false;
  }else{
    Trace("inst-engine") << "Added lemmas = " << (int)(d_quantEngine->getNumLemmasWaiting()-lastWaiting)  << std::endl;
    return true;
  }
}

bool InstantiationEngine::needsCheck( Theory::Effort e ){
  return d_quantEngine->getInstWhenNeedsCheck( e );
}

void InstantiationEngine::reset_round( Theory::Effort e ){
  //if not, proceed to instantiation round
  //reset the instantiation strategies
  for( unsigned i=0; i<d_instStrategies.size(); ++i ){
    InstStrategy* is = d_instStrategies[i];
    is->processResetInstantiationRound( e );
  }
}

void InstantiationEngine::check( Theory::Effort e, unsigned quant_e ){
  if( quant_e==QuantifiersEngine::QEFFORT_STANDARD ){
    double clSet = 0;
    if( Trace.isOn("inst-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "---Instantiation Engine Round, effort = " << e << "---" << std::endl;
    }
    //collect all active quantified formulas belonging to this
    bool quantActive = false;
    d_quants.clear();
    for( int i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( d_quantEngine->hasOwnership( q, this ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
        quantActive = true;
        d_quants.push_back( q );
      }
    }
    Trace("inst-engine-debug") << "InstEngine: check: # asserted quantifiers " << d_quants.size() << "/";
    Trace("inst-engine-debug") << d_quantEngine->getModel()->getNumAssertedQuantifiers() << " " << quantActive << std::endl;
    if( quantActive ){
      bool addedLemmas = doInstantiationRound( e );
      Trace("inst-engine-debug") << "Add lemmas = " << addedLemmas << std::endl;
    }else{
      d_quants.clear();
    }
    if( Trace.isOn("inst-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("inst-engine") << "Finished instantiation engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

bool InstantiationEngine::checkComplete() {
  if( !options::finiteModelFind() ){
    for( unsigned i=0; i<d_quants.size(); i++ ){
      if( isIncomplete( d_quants[i] ) ){
        return false;
      }
    }
  }
  return true;
}

bool InstantiationEngine::isIncomplete( Node q ) {
  return true;
}

void InstantiationEngine::registerQuantifier( Node f ){
  if( d_quantEngine->hasOwnership( f, this ) ){
    //for( unsigned i=0; i<d_instStrategies.size(); ++i ){
    //  d_instStrategies[i]->registerQuantifier( f );
    //}
    //take into account user patterns
    if( f.getNumChildren()==3 ){
      Node subsPat = d_quantEngine->getTermDatabase()->getInstConstantNode( f[2], f );
      //add patterns
      for( int i=0; i<(int)subsPat.getNumChildren(); i++ ){
        //Notice() << "Add pattern " << subsPat[i] << " for " << f << std::endl;
        if( subsPat[i].getKind()==INST_PATTERN ){
          addUserPattern( f, subsPat[i] );
        }else if( subsPat[i].getKind()==INST_NO_PATTERN ){
          addUserNoPattern( f, subsPat[i] );
        }
      }
    }
  }
}

void InstantiationEngine::addUserPattern( Node q, Node pat ){
  if( d_isup ){
    d_isup->addUserPattern( q, pat );
  }
}

void InstantiationEngine::addUserNoPattern( Node q, Node pat ){
  if( d_i_ag ){
    d_i_ag->addUserNoPattern( q, pat );
  }
}
