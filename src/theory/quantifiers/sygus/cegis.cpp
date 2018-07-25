/*********************                                                        */
/*! \file cegis.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of cegis
 **/

#include "theory/quantifiers/sygus/cegis.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Cegis::Cegis(QuantifiersEngine* qe, CegConjecture* p)
    : SygusModule(qe, p), d_eval_unfold(nullptr), d_using_gr_repair(false)
{
  if (options::sygusEvalUnfold())
  {
    d_eval_unfold = qe->getTermDatabaseSygus()->getEvalUnfold();
  }
}

bool Cegis::initialize(Node n,
                       const std::vector<Node>& candidates,
                       std::vector<Node>& lemmas)
{
  d_base_body = n;
  if (d_base_body.getKind() == NOT && d_base_body[0].getKind() == FORALL)
  {
    for (const Node& v : d_base_body[0][0])
    {
      d_base_vars.push_back(v);
    }
    d_base_body = d_base_body[0][1];
  }

  // assign the cegis sampler if applicable
  if (options::cegisSample() != CEGIS_SAMPLE_NONE)
  {
    Trace("cegis-sample") << "Initialize sampler for " << d_base_body << "..."
                          << std::endl;
    TypeNode bt = d_base_body.getType();
    d_cegis_sampler.initialize(bt, d_base_vars, options::sygusSamples());
  }
  return processInitialize(n, candidates, lemmas);
}

bool Cegis::processInitialize(Node n,
                              const std::vector<Node>& candidates,
                              std::vector<Node>& lemmas)
{
  Trace("cegis") << "Initialize cegis..." << std::endl;
  // initialize an enumerator for each candidate
  for (unsigned i = 0; i < candidates.size(); i++)
  {
    Trace("cegis") << "...register enumerator " << candidates[i];
    bool do_repair_const = false;
    if (options::sygusRepairConst())
    {
      TypeNode ctn = candidates[i].getType();
      d_tds->registerSygusType(ctn);
      if (d_tds->hasSubtermSymbolicCons(ctn))
      {
        do_repair_const = true;
        // remember that we are doing grammar-based repair
        d_using_gr_repair = true;
        Trace("cegis") << " (using repair)";
      }
    }
    Trace("cegis") << std::endl;
    d_tds->registerEnumerator(
        candidates[i], candidates[i], d_parent, false, do_repair_const);
  }
  return true;
}

void Cegis::getTermList(const std::vector<Node>& candidates,
                        std::vector<Node>& enums)
{
  enums.insert(enums.end(), candidates.begin(), candidates.end());
}

bool Cegis::addEvalLemmas(const std::vector<Node>& candidates,
                          const std::vector<Node>& candidate_values)
{
  NodeManager* nm = NodeManager::currentNM();
  bool addedEvalLemmas = false;
  if (options::sygusRefEval())
  {
    Trace("cegqi-engine") << "  *** Do refinement lemma evaluation..."
                          << std::endl;
    // see if any refinement lemma is refuted by evaluation
    std::vector<Node> cre_lems;
    getRefinementEvalLemmas(candidates, candidate_values, cre_lems);
    if (!cre_lems.empty())
    {
      for (const Node& lem : cre_lems)
      {
        if (d_qe->addLemma(lem))
        {
          Trace("cegqi-lemma")
              << "Cegqi::Lemma : ref evaluation : " << lem << std::endl;
          addedEvalLemmas = true;
        }
      }
      /* we could, but do not return here. experimentally, it is better to
         add the lemmas below as well, in parallel. */
    }
  }
  if (d_eval_unfold != nullptr)
  {
    Trace("cegqi-engine") << "  *** Do evaluation unfolding..." << std::endl;
    std::vector<Node> eager_terms, eager_vals, eager_exps;
    for (unsigned i = 0, size = candidates.size(); i < size; ++i)
    {
      Trace("cegqi-debug") << "  register " << candidates[i] << " -> "
                           << candidate_values[i] << std::endl;
      d_eval_unfold->registerModelValue(candidates[i],
                                        candidate_values[i],
                                        eager_terms,
                                        eager_vals,
                                        eager_exps);
    }
    Trace("cegqi-debug") << "...produced " << eager_terms.size()
                         << " evaluation unfold lemmas.\n";
    for (unsigned i = 0, size = eager_terms.size(); i < size; ++i)
    {
      Node lem = nm->mkNode(
          OR, eager_exps[i].negate(), eager_terms[i].eqNode(eager_vals[i]));
      if (d_qe->addLemma(lem))
      {
        Trace("cegqi-lemma")
            << "Cegqi::Lemma : evaluation unfold : " << lem << std::endl;
        addedEvalLemmas = true;
      }
    }
  }
  return addedEvalLemmas;
}

bool Cegis::constructCandidates(const std::vector<Node>& enums,
                                const std::vector<Node>& enum_values,
                                const std::vector<Node>& candidates,
                                std::vector<Node>& candidate_values,
                                std::vector<Node>& lems)
{
  if (Trace.isOn("cegis"))
  {
    Trace("cegis") << "  Enumerators :\n";
    for (unsigned i = 0, size = enums.size(); i < size; ++i)
    {
      Trace("cegis") << "    " << enums[i] << " -> ";
      std::stringstream ss;
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(ss, enum_values[i]);
      Trace("cegis") << ss.str() << std::endl;
    }
  }
  // if we are using grammar-based repair
  if (d_using_gr_repair)
  {
    SygusRepairConst* src = d_parent->getRepairConst();
    Assert(src != nullptr);
    // check if any enum_values have symbolic terms that must be repaired
    bool mustRepair = false;
    for (const Node& c : enum_values)
    {
      if (SygusRepairConst::mustRepair(c))
      {
        mustRepair = true;
        break;
      }
    }
    Trace("cegis") << "...must repair is: " << mustRepair << std::endl;
    // if the solution contains a subterm that must be repaired
    if (mustRepair)
    {
      std::vector<Node> fail_cvs = enum_values;
      Assert(candidates.size() == fail_cvs.size());
      if (src->repairSolution(candidates, fail_cvs, candidate_values))
      {
        return true;
      }
      // repair solution didn't work, exclude this solution
      std::vector<Node> exp;
      for (unsigned i = 0, size = enums.size(); i < size; i++)
      {
        d_tds->getExplain()->getExplanationForEquality(
            enums[i], enum_values[i], exp);
      }
      Assert(!exp.empty());
      Node expn =
          exp.size() == 1 ? exp[0] : NodeManager::currentNM()->mkNode(AND, exp);
      lems.push_back(expn.negate());
      return false;
    }
  }

  // evaluate on refinement lemmas
  bool addedEvalLemmas = addEvalLemmas(enums, enum_values);

  // try to construct candidates
  if (!processConstructCandidates(enums,
                                  enum_values,
                                  candidates,
                                  candidate_values,
                                  !addedEvalLemmas,
                                  lems))
  {
    return false;
  }

  if (options::cegisSample() != CEGIS_SAMPLE_NONE && lems.empty())
  {
    // if we didn't add a lemma, trying sampling to add a refinement lemma
    // that immediately refutes the candidate we just constructed
    if (sampleAddRefinementLemma(enums, enum_values, lems))
    {
      // restart (should be guaranteed to add evaluation lemmas on this call)
      return constructCandidates(
          enums, enum_values, candidates, candidate_values, lems);
    }
  }
  return true;
}

bool Cegis::processConstructCandidates(const std::vector<Node>& enums,
                                       const std::vector<Node>& enum_values,
                                       const std::vector<Node>& candidates,
                                       std::vector<Node>& candidate_values,
                                       bool satisfiedRl,
                                       std::vector<Node>& lems)
{
  if (satisfiedRl)
  {
    candidate_values.insert(
        candidate_values.end(), enum_values.begin(), enum_values.end());
    return true;
  }
  return false;
}

void Cegis::addRefinementLemma(Node lem)
{
  d_refinement_lemmas.push_back(lem);
  // apply existing substitution
  Node slem = lem;
  if (!d_rl_eval_hds.empty())
  {
    slem = lem.substitute(d_rl_eval_hds.begin(),
                          d_rl_eval_hds.end(),
                          d_rl_vals.begin(),
                          d_rl_vals.end());
  }
  // rewrite with extended rewriter
  slem = d_tds->getExtRewriter()->extendedRewrite(slem);
  std::vector<Node> waiting;
  waiting.push_back(lem);
  unsigned wcounter = 0;
  // while we are not done adding lemmas
  while (wcounter < waiting.size())
  {
    // add the conjunct, possibly propagating
    addRefinementLemmaConjunct(wcounter, waiting);
    wcounter++;
  }
}

void Cegis::addRefinementLemmaConjunct(unsigned wcounter,
                                       std::vector<Node>& waiting)
{
  Node lem = waiting[wcounter];
  lem = Rewriter::rewrite(lem);
  // apply substitution and rewrite if applicable
  if (lem.isConst())
  {
    if (!lem.getConst<bool>())
    {
      // conjecture is infeasible
    }
    else
    {
      return;
    }
  }
  // break into conjunctions
  if (lem.getKind() == AND)
  {
    for (const Node& lc : lem)
    {
      waiting.push_back(lc);
    }
    return;
  }
  // does this correspond to a substitution?
  NodeManager* nm = NodeManager::currentNM();
  TNode term;
  TNode val;
  if (lem.getKind() == EQUAL)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (lem[i].isConst() && d_tds->isEvaluationPoint(lem[1 - i]))
      {
        term = lem[1 - i];
        val = lem[i];
        break;
      }
    }
  }
  else
  {
    term = lem.getKind() == NOT ? lem[0] : lem;
    // predicate case: the conjunct is a (negated) evaluation point
    if (d_tds->isEvaluationPoint(term))
    {
      val = nm->mkConst(lem.getKind() != NOT);
    }
  }
  if (!val.isNull())
  {
    if (d_refinement_lemma_unit.find(lem) != d_refinement_lemma_unit.end())
    {
      // already added
      return;
    }
    Trace("cegis-rl") << "* cegis-rl: propagate: " << term << " -> " << val
                      << std::endl;
    d_rl_eval_hds.push_back(term);
    d_rl_vals.push_back(val);
    d_refinement_lemma_unit.insert(lem);
    // apply to waiting lemmas beyond this one
    for (unsigned i = wcounter + 1, size = waiting.size(); i < size; i++)
    {
      waiting[i] = waiting[i].substitute(term, val);
    }
    // apply to all existing refinement lemmas
    std::vector<Node> to_rem;
    for (const Node& rl : d_refinement_lemma_conj)
    {
      Node srl = rl.substitute(term, val);
      if (srl != rl)
      {
        Trace("cegis-rl") << "* cegis-rl: replace: " << rl << " -> " << srl
                          << std::endl;
        waiting.push_back(srl);
        to_rem.push_back(rl);
      }
    }
    for (const Node& tr : to_rem)
    {
      d_refinement_lemma_conj.erase(tr);
    }
  }
  else
  {
    if (Trace.isOn("cegis-rl"))
    {
      if (d_refinement_lemma_conj.find(lem) == d_refinement_lemma_conj.end())
      {
        Trace("cegis-rl") << "cegis-rl: add: " << lem << std::endl;
      }
    }
    d_refinement_lemma_conj.insert(lem);
  }
}

void Cegis::registerRefinementLemma(const std::vector<Node>& vars,
                                    Node lem,
                                    std::vector<Node>& lems)
{
  addRefinementLemma(lem);
  // Make the refinement lemma and add it to lems.
  // This lemma is guarded by the parent's guard, which has the semantics
  // "this conjecture has a solution", hence this lemma states:
  // if the parent conjecture has a solution, it satisfies the specification
  // for the given concrete point.
  Node rlem =
      NodeManager::currentNM()->mkNode(OR, d_parent->getGuard().negate(), lem);
  lems.push_back(rlem);
}

bool Cegis::usingRepairConst() { return true; }

void Cegis::getRefinementEvalLemmas(const std::vector<Node>& vs,
                                    const std::vector<Node>& ms,
                                    std::vector<Node>& lems)
{
  Trace("sygus-cref-eval") << "Cref eval : conjecture has "
                           << d_refinement_lemma_unit.size() << " unit and "
                           << d_refinement_lemma_conj.size()
                           << " non-unit refinement lemma conjunctions."
                           << std::endl;
  Assert(vs.size() == ms.size());

  NodeManager* nm = NodeManager::currentNM();

  Node nfalse = nm->mkConst(false);
  Node neg_guard = d_parent->getGuard().negate();
  for (unsigned r = 0; r < 2; r++)
  {
    std::unordered_set<Node, NodeHashFunction>& rlemmas =
        r == 0 ? d_refinement_lemma_unit : d_refinement_lemma_conj;
    for (const Node& lem : rlemmas)
    {
      Assert(!lem.isNull());
      std::map<Node, Node> visited;
      std::map<Node, std::vector<Node> > exp;
      EvalSygusInvarianceTest vsit;
      Trace("sygus-cref-eval") << "Check refinement lemma conjunct " << lem
                               << " against current model." << std::endl;
      Trace("sygus-cref-eval2") << "Check refinement lemma conjunct " << lem
                                << " against current model." << std::endl;
      Node cre_lem;
      Node lemcs = lem.substitute(vs.begin(), vs.end(), ms.begin(), ms.end());
      Trace("sygus-cref-eval2")
          << "...under substitution it is : " << lemcs << std::endl;
      Node lemcsu = vsit.doEvaluateWithUnfolding(d_tds, lemcs);
      Trace("sygus-cref-eval2")
          << "...after unfolding is : " << lemcsu << std::endl;
      if (lemcsu.isConst() && !lemcsu.getConst<bool>())
      {
        std::vector<Node> msu;
        std::vector<Node> mexp;
        msu.insert(msu.end(), ms.begin(), ms.end());
        std::map<TypeNode, int> var_count;
        for (unsigned k = 0; k < vs.size(); k++)
        {
          vsit.setUpdatedTerm(msu[k]);
          msu[k] = vs[k];
          // substitute for everything except this
          Node sconj =
              lem.substitute(vs.begin(), vs.end(), msu.begin(), msu.end());
          vsit.init(sconj, vs[k], nfalse);
          // get minimal explanation for this
          Node ut = vsit.getUpdatedTerm();
          Trace("sygus-cref-eval2-debug")
              << "  compute min explain of : " << vs[k] << " = " << ut
              << std::endl;
          d_tds->getExplain()->getExplanationFor(
              vs[k], ut, mexp, vsit, var_count, false);
          Trace("sygus-cref-eval2-debug") << "exp now: " << mexp << std::endl;
          msu[k] = vsit.getUpdatedTerm();
          Trace("sygus-cref-eval2-debug")
              << "updated term : " << msu[k] << std::endl;
        }
        if (!mexp.empty())
        {
          Node en = mexp.size() == 1 ? mexp[0] : nm->mkNode(kind::AND, mexp);
          cre_lem = nm->mkNode(kind::OR, en.negate(), neg_guard);
        }
        else
        {
          cre_lem = neg_guard;
        }
      }
      if (!cre_lem.isNull()
          && std::find(lems.begin(), lems.end(), cre_lem) == lems.end())
      {
        Trace("sygus-cref-eval")
            << "...produced lemma : " << cre_lem << std::endl;
        lems.push_back(cre_lem);
      }
    }
    if (!lems.empty())
    {
      break;
    }
  }
}

bool Cegis::sampleAddRefinementLemma(const std::vector<Node>& candidates,
                                     const std::vector<Node>& vals,
                                     std::vector<Node>& lems)
{
  Trace("cegqi-engine") << "  *** Do sample add refinement..." << std::endl;
  if (Trace.isOn("cegis-sample"))
  {
    Trace("cegis-sample") << "Check sampling for candidate solution"
                          << std::endl;
    for (unsigned i = 0, size = vals.size(); i < size; i++)
    {
      Trace("cegis-sample") << "  " << candidates[i] << " -> " << vals[i]
                            << std::endl;
    }
  }
  Assert(vals.size() == candidates.size());
  Node sbody = d_base_body.substitute(
      candidates.begin(), candidates.end(), vals.begin(), vals.end());
  Trace("cegis-sample-debug") << "Sample " << sbody << std::endl;
  // do eager unfolding
  std::map<Node, Node> visited_n;
  sbody = d_qe->getTermDatabaseSygus()->getEagerUnfold(sbody, visited_n);
  Trace("cegis-sample") << "Sample (after unfolding): " << sbody << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = d_cegis_sampler.getNumSamplePoints(); i < size;
       i++)
  {
    if (d_cegis_sample_refine.find(i) == d_cegis_sample_refine.end())
    {
      Node ev = d_cegis_sampler.evaluate(sbody, i);
      Trace("cegis-sample-debug") << "...evaluate point #" << i << " to " << ev
                                  << std::endl;
      Assert(ev.isConst());
      Assert(ev.getType().isBoolean());
      if (!ev.getConst<bool>())
      {
        Trace("cegis-sample-debug") << "...false for point #" << i << std::endl;
        // mark this as a CEGIS point (no longer sampled)
        d_cegis_sample_refine.insert(i);
        std::vector<Node> vars;
        std::vector<Node> pt;
        d_cegis_sampler.getSamplePoint(i, vars, pt);
        Assert(d_base_vars.size() == pt.size());
        Node rlem = d_base_body.substitute(
            d_base_vars.begin(), d_base_vars.end(), pt.begin(), pt.end());
        rlem = Rewriter::rewrite(rlem);
        if (std::find(
                d_refinement_lemmas.begin(), d_refinement_lemmas.end(), rlem)
            == d_refinement_lemmas.end())
        {
          if (Trace.isOn("cegis-sample"))
          {
            Trace("cegis-sample") << "   false for point #" << i << " : ";
            for (const Node& cn : pt)
            {
              Trace("cegis-sample") << cn << " ";
            }
            Trace("cegis-sample") << std::endl;
          }
          Trace("cegqi-engine") << "  *** Refine by sampling" << std::endl;
          addRefinementLemma(rlem);
          // if trust, we are not interested in sending out refinement lemmas
          if (options::cegisSample() != CEGIS_SAMPLE_TRUST)
          {
            Node lem = nm->mkNode(OR, d_parent->getGuard().negate(), rlem);
            lems.push_back(lem);
          }
          return true;
        }
        else
        {
          Trace("cegis-sample-debug") << "...duplicate." << std::endl;
        }
      }
    }
  }
  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
