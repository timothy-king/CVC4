/*********************                                                        */
/*! \file type_checker_template.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): lianah
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief TypeChecker implementation
 **
 ** TypeChecker implementation.
 **/

#line 18 "${template}"

#include "expr/type_checker.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"

${typechecker_includes}

#line 26 "${template}"

namespace CVC4 {
namespace expr {

TypeNode TypeChecker::computeType(NodeManager* nodeManager, TNode n, bool check)
  throw (TypeCheckingExceptionPrivate, AssertionException) {
  TypeNode typeNode;

  // Infer the type
  switch(n.getKind()) {
  case kind::VARIABLE:
  case kind::SKOLEM:
    typeNode = nodeManager->getAttribute(n, TypeAttr());
    break;
  case kind::BUILTIN:
    typeNode = nodeManager->builtinOperatorType();
    break;
  case kind::BITVECTOR_EXTRACT_OP :
    typeNode = nodeManager->builtinOperatorType();
    break; 

${typerules}

#line 50 "${template}"

  default:
    Debug("getType") << "FAILURE" << std::endl;
    Unhandled(n.getKind());
  }

  nodeManager->setAttribute(n, TypeAttr(), typeNode);
  nodeManager->setAttribute(n, TypeCheckedAttr(),
                            check || nodeManager->getAttribute(n, TypeCheckedAttr()));

  return typeNode;

}/* TypeChecker::computeType */

bool TypeChecker::computeIsConst(NodeManager* nodeManager, TNode n)
  throw (AssertionException) {

  Assert(n.getMetaKind() == kind::metakind::OPERATOR || n.getMetaKind() == kind::metakind::PARAMETERIZED);

  switch(n.getKind()) {
${construles}

#line 73 "${template}"

  default:;
  }

  return false;

}/* TypeChecker::computeIsConst */

bool TypeChecker::neverIsConst(NodeManager* nodeManager, TNode n)
  throw (AssertionException) {

  Assert(n.getMetaKind() == kind::metakind::OPERATOR || n.getMetaKind() == kind::metakind::PARAMETERIZED);

  switch(n.getKind()) {
${neverconstrules}

#line 89 "${template}"

  default:;
  }

  return true;

}/* TypeChecker::neverIsConst */

}/* CVC4::expr namespace */
}/* CVC4 namespace */
