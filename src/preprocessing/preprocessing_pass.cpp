/*********************                                                        */
/*! \file preprocessing_pass.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Justin Xu, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass super class
 **
 ** Preprocessing pass super class.
 **/

#include "preprocessing/preprocessing_pass.h"

#include "expr/node_manager.h"
#include "proof/proof.h"
#include "smt/dump.h"
#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace preprocessing {

AssertionPipeline::AssertionPipeline(context::Context* context)
    : d_substitutionsIndex(context, 0), d_topLevelSubstitutions(context)
{
}

void AssertionPipeline::replace(size_t i, Node n) {
  PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]););
  d_nodes[i] = n;
}

void AssertionPipeline::replace(size_t i,
                                Node n,
                                const std::vector<Node>& addnDeps)
{
  PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]);
        for (const auto& addnDep
             : addnDeps) {
          ProofManager::currentPM()->addDependence(n, addnDep);
        });
  d_nodes[i] = n;
}

void AssertionPipeline::replace(size_t i, const std::vector<Node>& ns)
{
  PROOF(
      for (const auto& n
           : ns) { ProofManager::currentPM()->addDependence(n, d_nodes[i]); });
  d_nodes[i] = NodeManager::currentNM()->mkConst<bool>(true);

  for (const auto& n : ns)
  {
    d_nodes.push_back(n);
  }
}

PreprocessingPassResult PreprocessingPass::apply(
    AssertionPipeline* assertionsToPreprocess) {
  TimerStat::CodeTimer codeTimer(d_timer);
  Trace("preprocessing") << "PRE " << d_name << std::endl;
  Chat() << d_name << "..." << std::endl;
  dumpAssertions(("pre-" + d_name).c_str(), *assertionsToPreprocess);
  PreprocessingPassResult result = applyInternal(assertionsToPreprocess);
  dumpAssertions(("post-" + d_name).c_str(), *assertionsToPreprocess);
  Trace("preprocessing") << "POST " << d_name << std::endl;
  return result;
}

void PreprocessingPass::dumpAssertions(const char* key,
                                       const AssertionPipeline& assertionList) {
  if (Dump.isOn("assertions") && Dump.isOn(std::string("assertions::") + key)) {
    // Push the simplified assertions to the dump output stream
    for (const auto& n : assertionList) {
      Dump("assertions") << AssertCommand(Expr(n.toExpr()));
    }
  }
}

PreprocessingPass::PreprocessingPass(PreprocessingPassContext* preprocContext,
                                     const std::string& name)
    : d_name(name), d_timer("preprocessing::" + name) {
  d_preprocContext = preprocContext;
  smtStatisticsRegistry()->registerStat(&d_timer);
}

PreprocessingPass::~PreprocessingPass() {
  Assert(smt::smtEngineInScope());
  if (smtStatisticsRegistry() != nullptr) {
    smtStatisticsRegistry()->unregisterStat(&d_timer);
  }
}

}  // namespace preprocessing
}  // namespace CVC4
