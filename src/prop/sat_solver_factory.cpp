/*********************                                                        */
/*! \file sat_solver_factory.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Tim King
 ** Minor contributors (to current version): Morgan Deters, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver creation facility.
 **
 ** SAT Solver.
 **/

#include "prop/sat_solver_factory.h"

#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"

namespace CVC4 {
namespace prop {

BVSatSolverInterface* SatSolverFactory::createMinisat(context::Context* mainSatContext, StatisticsRegistry* registry, const std::string& name) {
  return new BVMinisatSatSolver(registry, mainSatContext, name);
}

DPLLSatSolverInterface* SatSolverFactory::createDPLLMinisat(StatisticsRegistry* registry) {
  return new MinisatSatSolver(registry);
}

} /* CVC4::prop namespace */
} /* CVC4 namespace */
