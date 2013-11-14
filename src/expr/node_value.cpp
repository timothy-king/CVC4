/*********************                                                        */
/*! \file node_value.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An expression node.
 **
 ** An expression node.
 **
 ** Instances of this class are generally referenced through
 ** cvc4::Node rather than by pointer; cvc4::Node maintains the
 ** reference count on NodeValue instances and
 **/

#include "expr/node_value.h"
#include "expr/node.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "util/language.h"
#include "options/options.h"
#include "printer/printer.h"
#include <sstream>

using namespace std;

namespace CVC4 {
namespace expr {

NodeValue NodeValue::s_null(0);

string NodeValue::toString() const {
  stringstream ss;

  OutputLanguage outlang = (this == &s_null) ? language::output::LANG_AST : options::outputLanguage();
  toStream(ss, -1, false, false,
           outlang == language::output::LANG_AUTO ?
             language::output::LANG_AST :
             outlang);
  return ss.str();
}

void NodeValue::toStream(std::ostream& out, int toDepth, bool types, size_t dag,
                         OutputLanguage language) const {
  // Ensure that this node value is live for the length of this call.
  // It really breaks things badly if we don't have a nonzero ref
  // count, even just for printing.
  RefCountGuard guard(this);

  Printer::getPrinter(language)->toStream(out, TNode(this), toDepth, types, dag);
}

void NodeValue::printAst(std::ostream& out, int ind) const {
  RefCountGuard guard(this);

  indent(out, ind);
  out << '(';
  out << getKind();
  if(getMetaKind() == kind::metakind::VARIABLE) {
    out << ' ' << getId();
  } else if(getMetaKind() == kind::metakind::CONSTANT) {
    out << ' ';
    kind::metakind::NodeValueConstPrinter::toStream(out, this);
  } else {
    if(nv_begin() != nv_end()) {
      for(const_nv_iterator child = nv_begin(); child != nv_end(); ++child) {
        out << std::endl;
        (*child)->printAst(out, ind + 1);
      }
      out << std::endl;
      indent(out, ind);
    }
  }
  out << ')';
}

unsigned NodeValue::getRefCount() const {
  switch(d_rc){
  case STICKY_RC: return MAXIMUM_RC;
  case MANAGED_RC:
    Assert(NodeManager::currentNM() != NULL,
           "No current NodeManager when getting a managed ref count of NodeValue");
    return NodeManager::currentNM()->getManagedRefCount(this);
  default: return d_rc;
  }
}

NodeValue::RefCountGuard::RefCountGuard(const NodeValue* nv) :
  d_nv(const_cast<NodeValue*>(nv)) {
  // inc()
  if(__builtin_expect( ( d_nv->d_rc < MANAGED_RC ), true )) {
    ++d_nv->d_rc;
  }else if(__builtin_expect( ( d_nv->d_rc == MANAGED_RC ), false )){
    Assert(NodeManager::currentNM() != NULL,
           "No current NodeManager when incrementing a managed ref count of NodeValue");
    d_nv->d_rc = NodeManager::currentNM()->incrementManagedRefCount(d_nv);
  }
}

NodeValue::RefCountGuard::~RefCountGuard() {
  // dec() without marking for deletion: we don't want to garbage
  // collect this NodeValue if ours is the last reference to it.
  // E.g., this can happen when debugging code calls the print
  // routines below.  As RefCountGuards are scoped on the stack,
  // this should be fine---but not in multithreaded contexts!
  if(__builtin_expect( ( d_nv->d_rc < MANAGED_RC ), true )) {
    --d_nv->d_rc;
  }else if(__builtin_expect( ( d_nv->d_rc == MANAGED_RC ), true )){
    Assert(NodeManager::currentNM() != NULL,
           "No current NodeManager when incrementing a managed ref count of NodeValue");
    d_nv->d_rc = NodeManager::currentNM()->decrementManagedRefCount(d_nv);
  }
}


}/* CVC4::expr namespace */
}/* CVC4 namespace */
