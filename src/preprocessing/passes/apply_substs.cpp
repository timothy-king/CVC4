/*********************                                                        */
/*! \file apply_substs.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Apply substitutions preprocessing pass.
 **
 ** Apply top level substitutions to assertions, rewrite, and store back into
 ** assertions.
 **/

#include "preprocessing/passes/apply_substs.h"

#include "context/cdo.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

ApplySubsts::ApplySubsts(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "apply-substs")
{
}

PreprocessingPassResult ApplySubsts::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  if (!options::unsatCores())
  {
    Chat() << "applying substitutions..." << std::endl;
    Trace("apply-substs") << "SmtEnginePrivate::processAssertions(): "
                      << "applying substitutions" << std::endl;
    // TODO(#1255): Substitutions in incremental mode should be managed with a
    // proper data structure.

    // When solving incrementally, all substitutions are piled into the
    // assertion at d_substitutionsIndex: we don't want to apply substitutions
    // to this assertion or information will be lost.
    context::CDO<unsigned>& substs_index =
        assertionsToPreprocess->getSubstitutionsIndex();
    unsigned size = assertionsToPreprocess->size();
    unsigned substitutionAssertion = substs_index > 0 ? substs_index : size;
    for (unsigned i = 0; i < size; ++i)
    {
      if (i == substitutionAssertion)
      {
        continue;
      }
      Trace("apply-substs") << "applying to " << (*assertionsToPreprocess)[i]
                        << std::endl;
      d_preprocContext->spendResource(options::preprocessStep());
      assertionsToPreprocess->replace(
          i,
          theory::Rewriter::rewrite(
              assertionsToPreprocess->getTopLevelSubstitutions().apply(
                  (*assertionsToPreprocess)[i])));
      Trace("apply-substs") << "  got " << (*assertionsToPreprocess)[i]
                        << std::endl;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
