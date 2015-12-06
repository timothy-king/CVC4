/*********************                                                        */
/*! \file datatype.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A class representing a Datatype definition
 **
 ** A class representing a Datatype definition for the theory of
 ** inductive datatypes.
 **/

#include <string>
#include <sstream>

#include "base/cvc4_assert.h"
#include "expr/type.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/node_manager.h"
#include "expr/node.h"
#include "expr/attribute.h"
#include "util/datatype.h"
#include "util/matcher.h"

using namespace std;

namespace CVC4 {

namespace expr {
  namespace attr {
    struct DatatypeIndexTag {};
    struct DatatypeConsIndexTag {};
    struct DatatypeFiniteTag {};
    struct DatatypeFiniteComputedTag {};
  }/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

typedef expr::Attribute<expr::attr::DatatypeIndexTag, uint64_t> DatatypeIndexAttr;
typedef expr::Attribute<expr::attr::DatatypeConsIndexTag, uint64_t> DatatypeConsIndexAttr;
typedef expr::Attribute<expr::attr::DatatypeFiniteTag, bool> DatatypeFiniteAttr;
typedef expr::Attribute<expr::attr::DatatypeFiniteComputedTag, bool> DatatypeFiniteComputedAttr;

const Datatype& Datatype::datatypeOf(Expr item) {
  ExprManagerScope ems(item);
  TypeNode t = Node::fromExpr(item).getType();
  switch(t.getKind()) {
  case kind::CONSTRUCTOR_TYPE:
    return DatatypeType(t[t.getNumChildren() - 1].toType()).getDatatype();
  case kind::SELECTOR_TYPE:
  case kind::TESTER_TYPE:
    return DatatypeType(t[0].toType()).getDatatype();
  default:
    Unhandled("arg must be a datatype constructor, selector, or tester");
  }
}

size_t Datatype::indexOf(Expr item) {
  ExprManagerScope ems(item);
  CheckArgument(item.getType().isConstructor() ||
                item.getType().isTester() ||
                item.getType().isSelector(),
                item,
                "arg must be a datatype constructor, selector, or tester");
  TNode n = Node::fromExpr(item);
  if( item.getKind()==kind::APPLY_TYPE_ASCRIPTION ){
    return indexOf( item[0] );
  }else{
    Assert(n.hasAttribute(DatatypeIndexAttr()));
    return n.getAttribute(DatatypeIndexAttr());
  }
}

size_t Datatype::cindexOf(Expr item) {
  ExprManagerScope ems(item);
  CheckArgument(item.getType().isSelector(),
                item,
                "arg must be a datatype selector");
  TNode n = Node::fromExpr(item);
  if( item.getKind()==kind::APPLY_TYPE_ASCRIPTION ){
    return cindexOf( item[0] );
  }else{
    Assert(n.hasAttribute(DatatypeConsIndexAttr()));
    return n.getAttribute(DatatypeConsIndexAttr());
  }
}

void Datatype::resolve(ExprManager* em,
                       const std::map<std::string, DatatypeType>& resolutions,
                       const std::vector<Type>& placeholders,
                       const std::vector<Type>& replacements,
                       const std::vector< SortConstructorType >& paramTypes,
                       const std::vector< DatatypeType >& paramReplacements)
  throw(IllegalArgumentException, DatatypeResolutionException) {

  CheckArgument(em != NULL, em, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!d_resolved, this, "cannot resolve a Datatype twice");
  CheckArgument(resolutions.find(d_name) != resolutions.end(), resolutions,
                "Datatype::resolve(): resolutions doesn't contain me!");
  CheckArgument(placeholders.size() == replacements.size(), placeholders,
                "placeholders and replacements must be the same size");
  CheckArgument(paramTypes.size() == paramReplacements.size(), paramTypes,
                "paramTypes and paramReplacements must be the same size");
  CheckArgument(getNumConstructors() > 0, *this, "cannot resolve a Datatype that has no constructors");
  DatatypeType self = (*resolutions.find(d_name)).second;
  CheckArgument(&self.getDatatype() == this, resolutions, "Datatype::resolve(): resolutions doesn't contain me!");
  d_resolved = true;
  size_t index = 0;
  for(std::vector<DatatypeConstructor>::iterator i = d_constructors.begin(), i_end = d_constructors.end(); i != i_end; ++i) {
    (*i).resolve(em, self, resolutions, placeholders, replacements, paramTypes, paramReplacements, index);
    Node::fromExpr((*i).d_constructor).setAttribute(DatatypeIndexAttr(), index);
    Node::fromExpr((*i).d_tester).setAttribute(DatatypeIndexAttr(), index++);
  }
  d_self = self;

  d_involvesExt =  false;
  for(const_iterator i = begin(); i != end(); ++i) {
    if( (*i).involvesExternalType() ){
      d_involvesExt =  true;
      break;
    }
  }
}

void Datatype::addConstructor(const DatatypeConstructor& c) {
  CheckArgument(!d_resolved, this,
                "cannot add a constructor to a finalized Datatype");
  d_constructors.push_back(c);
}


void Datatype::setSygus( Type st, Expr bvl, bool allow_const, bool allow_all ){
  CheckArgument(!d_resolved, this,
                "cannot set sygus type to a finalized Datatype");
  d_sygus_type = st;
  d_sygus_bvl = bvl;
  d_sygus_allow_const = allow_const || allow_all;
  d_sygus_allow_all = allow_all;
}


Cardinality Datatype::getCardinality() const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");
  std::vector< Type > processing;
  computeCardinality( processing );
  return d_card;
}

Cardinality Datatype::computeCardinality( std::vector< Type >& processing ) const throw(IllegalArgumentException){
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if( std::find( processing.begin(), processing.end(), d_self )!=processing.end() ){
    d_card = Cardinality::INTEGERS;
  }else{
    processing.push_back( d_self );
    Cardinality c = 0;
    for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
      c += (*i).computeCardinality( processing );
    }
    d_card = c;
    processing.pop_back();
  }
  return d_card;
}

bool Datatype::isRecursiveSingleton() const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if( d_card_rec_singleton==0 ){
    Assert( d_card_u_assume.empty() );
    std::vector< Type > processing;
    if( computeCardinalityRecSingleton( processing, d_card_u_assume ) ){
      d_card_rec_singleton = 1;
    }else{
      d_card_rec_singleton = -1;
    }
    if( d_card_rec_singleton==1 ){
      Trace("dt-card") << "Datatype " << getName() << " is recursive singleton, dependent upon " << d_card_u_assume.size() << " uninterpreted sorts: " << std::endl;
      for( unsigned i=0; i<d_card_u_assume.size(); i++ ){
        Trace("dt-card") << "  " << d_card_u_assume [i] << std::endl;
      }
      Trace("dt-card") << std::endl;
    }
  }
  return d_card_rec_singleton==1;
}

unsigned Datatype::getNumRecursiveSingletonArgTypes() const throw(IllegalArgumentException) {
  return d_card_u_assume.size();
}
Type Datatype::getRecursiveSingletonArgType( unsigned i ) const throw(IllegalArgumentException) {
  return d_card_u_assume[i];
}

bool Datatype::computeCardinalityRecSingleton( std::vector< Type >& processing, std::vector< Type >& u_assume ) const throw(IllegalArgumentException){
  if( std::find( processing.begin(), processing.end(), d_self )!=processing.end() ){
    return true;
  }else{
    if( d_card_rec_singleton==0 ){
      //if not yet computed
      if( d_constructors.size()==1 ){
        bool success = false;
        processing.push_back( d_self );
        for(unsigned i = 0; i<d_constructors[0].getNumArgs(); i++ ) {
          Type t = ((SelectorType)d_constructors[0][i].getType()).getRangeType();
          //if it is an uninterpreted sort, then we depend on it having cardinality one
          if( t.isSort() ){
            if( std::find( u_assume.begin(), u_assume.end(), t )==u_assume.end() ){
              u_assume.push_back( t );
            }
          //if it is a datatype, recurse
          }else if( t.isDatatype() ){
            const Datatype & dt = ((DatatypeType)t).getDatatype();
            if( !dt.computeCardinalityRecSingleton( processing, u_assume ) ){
              return false;
            }else{
              success = true;
            }
          //if it is a builtin type, it must have cardinality one
          }else if( !t.getCardinality().isOne() ){
            return false;
          }
        }
        processing.pop_back();
        return success;
      }else{
        return false;
      }
    }else if( d_card_rec_singleton==-1 ){
      return false;
    }else{
      for( unsigned i=0; i<d_card_u_assume.size(); i++ ){
        if( std::find( u_assume.begin(), u_assume.end(), d_card_u_assume[i] )==u_assume.end() ){
          u_assume.push_back( d_card_u_assume[i] );
        }
      }
      return true;
    }
  }
}

bool Datatype::isFinite() const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_self);

  TypeNode self = TypeNode::fromType(d_self);

  // is this already in the cache ?
  if(self.getAttribute(DatatypeFiniteComputedAttr())) {
    return self.getAttribute(DatatypeFiniteAttr());
  }

  Cardinality c = 0;
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if(! (*i).isFinite()) {
      self.setAttribute(DatatypeFiniteComputedAttr(), true);
      self.setAttribute(DatatypeFiniteAttr(), false);
      return false;
    }
  }
  self.setAttribute(DatatypeFiniteComputedAttr(), true);
  self.setAttribute(DatatypeFiniteAttr(), true);
  return true;
}

bool Datatype::isWellFounded() const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if( d_well_founded==0 ){
    // we're using some internals, so we have to set up this library context
    ExprManagerScope ems(d_self);
    std::vector< Type > processing;
    if( computeWellFounded( processing ) ){
      d_well_founded = 1;
    }else{
      d_well_founded = -1;
    }
  }
  return d_well_founded==1;
}

bool Datatype::computeWellFounded( std::vector< Type >& processing ) const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");
  if( std::find( processing.begin(), processing.end(), d_self )!=processing.end() ){
    return d_isCo;
  }else{
    processing.push_back( d_self );
    for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
      if( (*i).computeWellFounded( processing ) ){
        processing.pop_back();
        return true;
      }else{
        Trace("dt-wf") << "Constructor " << (*i).getName() << " is not well-founded." << std::endl;
      }
    }
    processing.pop_back();
    Trace("dt-wf") << "Datatype " << getName() << " is not well-founded." << std::endl;
    return false;
  }
}

Expr Datatype::mkGroundTerm( Type t ) const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype is not yet resolved");
  ExprManagerScope ems(d_self);


  // is this already in the cache ?
  std::map< Type, Expr >::iterator it = d_ground_term.find( t );
  if( it != d_ground_term.end() ){
    Debug("datatypes") << "\nin cache: " << d_self << " => " << it->second << std::endl;
    return it->second;
  } else {
    std::vector< Type > processing;
    Expr groundTerm = computeGroundTerm( t, processing );
    if(!groundTerm.isNull() ) {
      // we found a ground-term-constructing constructor!
      d_ground_term[t] = groundTerm;
      Debug("datatypes") << "constructed: " << getName() << " => " << groundTerm << std::endl;
    }
    if( groundTerm.isNull() ){
      if( !d_isCo ){
        // if we get all the way here, we aren't well-founded
        CheckArgument(false, *this, "datatype is not well-founded, cannot construct a ground term!");
      }else{
        return groundTerm;
      }
    }else{
      return groundTerm;
    }
  }
}

Expr getSubtermWithType( Expr e, Type t, bool isTop ){
  if( !isTop && e.getType()==t ){
    return e;
  }else{
    for( unsigned i=0; i<e.getNumChildren(); i++ ){
      Expr se = getSubtermWithType( e[i], t, false );
      if( !se.isNull() ){
        return se;
      }
    }
    return Expr();
  }
}

Expr Datatype::computeGroundTerm( Type t, std::vector< Type >& processing ) const throw(IllegalArgumentException) {
  if( std::find( processing.begin(), processing.end(), d_self )==processing.end() ){
    processing.push_back( d_self );
    for( unsigned r=0; r<2; r++ ){
      for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
        //do nullary constructors first
        if( ((*i).getNumArgs()==0)==(r==0)){
          Debug("datatypes") << "Try constructing for " << (*i).getName() << ", processing = " << processing.size() << std::endl;
          Expr e = (*i).computeGroundTerm( t, processing, d_ground_term );
          if( !e.isNull() ){
            //must check subterms for the same type to avoid infinite loops in type enumeration
            Expr se = getSubtermWithType( e, t, true );
            if( !se.isNull() ){
              Debug("datatypes") << "Take subterm " << se << std::endl;
              e = se;
            }
            processing.pop_back();
            return e;
          }else{
            Debug("datatypes") << "...failed." << std::endl;
          }
        }
      }
    }
    processing.pop_back();
  }else{
    Debug("datatypes") << "...already processing " << t << std::endl;
  }
  return Expr();
}

DatatypeType Datatype::getDatatypeType() const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  CheckArgument(!d_self.isNull(), *this);
  return DatatypeType(d_self);
}

DatatypeType Datatype::getDatatypeType(const std::vector<Type>& params)
  const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), *this, "Datatype must be resolved to get its DatatypeType");
  CheckArgument(!d_self.isNull() && DatatypeType(d_self).isParametric(), this);
  return DatatypeType(d_self).instantiate(params);
}

bool Datatype::operator==(const Datatype& other) const throw() {
  // two datatypes are == iff the name is the same and they have
  // exactly matching constructors (in the same order)

  if(this == &other) {
    return true;
  }

  if(isResolved() != other.isResolved()) {
    return false;
  }

  if( d_name != other.d_name ||
      getNumConstructors() != other.getNumConstructors() ) {
    return false;
  }
  for(const_iterator i = begin(), j = other.begin(); i != end(); ++i, ++j) {
    Assert(j != other.end());
    // two constructors are == iff they have the same name, their
    // constructors and testers are equal and they have exactly
    // matching args (in the same order)
    if((*i).getName() != (*j).getName() ||
       (*i).getNumArgs() != (*j).getNumArgs()) {
      return false;
    }
    // testing equivalence of constructors and testers is harder b/c
    // this constructor might not be resolved yet; only compare them
    // if they are both resolved
    Assert(isResolved() == !(*i).d_constructor.isNull() &&
           isResolved() == !(*i).d_tester.isNull() &&
           (*i).d_constructor.isNull() == (*j).d_constructor.isNull() &&
           (*i).d_tester.isNull() == (*j).d_tester.isNull());
    if(!(*i).d_constructor.isNull() && (*i).d_constructor != (*j).d_constructor) {
      return false;
    }
    if(!(*i).d_tester.isNull() && (*i).d_tester != (*j).d_tester) {
      return false;
    }
    for(DatatypeConstructor::const_iterator k = (*i).begin(), l = (*j).begin(); k != (*i).end(); ++k, ++l) {
      Assert(l != (*j).end());
      if((*k).getName() != (*l).getName()) {
        return false;
      }
      // testing equivalence of selectors is harder b/c args might not
      // be resolved yet
      Assert(isResolved() == (*k).isResolved() &&
             (*k).isResolved() == (*l).isResolved());
      if((*k).isResolved()) {
        // both are resolved, so simply compare the selectors directly
        if((*k).d_selector != (*l).d_selector) {
          return false;
        }
      } else {
        // neither is resolved, so compare their (possibly unresolved)
        // types; we don't know if they'll be resolved the same way,
        // so we can't ever say unresolved types are equal
        if(!(*k).d_selector.isNull() && !(*l).d_selector.isNull()) {
          if((*k).d_selector.getType() != (*l).d_selector.getType()) {
            return false;
          }
        } else {
          if((*k).isUnresolvedSelf() && (*l).isUnresolvedSelf()) {
            // Fine, the selectors are equal if the rest of the
            // enclosing datatypes are equal...
          } else {
            return false;
          }
        }
      }
    }
  }
  return true;
}

const DatatypeConstructor& Datatype::operator[](size_t index) const {
  CheckArgument(index < getNumConstructors(), index, "index out of bounds");
  return d_constructors[index];
}

const DatatypeConstructor& Datatype::operator[](std::string name) const {
  for(const_iterator i = begin(); i != end(); ++i) {
    if((*i).getName() == name) {
      return *i;
    }
  }
  CheckArgument(false, name, "No such constructor `%s' of datatype `%s'", name.c_str(), d_name.c_str());
}

Expr Datatype::getConstructor(std::string name) const {
  return (*this)[name].getConstructor();
}

Type Datatype::getSygusType() const {
  return d_sygus_type;
}

Expr Datatype::getSygusVarList() const {
  return d_sygus_bvl;
}

bool Datatype::getSygusAllowConst() const {
  return d_sygus_allow_const;
}

bool Datatype::getSygusAllowAll() const {
  return d_sygus_allow_const;
}

bool Datatype::involvesExternalType() const{
  return d_involvesExt;
}

void DatatypeConstructor::resolve(ExprManager* em, DatatypeType self,
                                  const std::map<std::string, DatatypeType>& resolutions,
                                  const std::vector<Type>& placeholders,
                                  const std::vector<Type>& replacements,
                                  const std::vector< SortConstructorType >& paramTypes,
                                  const std::vector< DatatypeType >& paramReplacements, size_t cindex)
  throw(IllegalArgumentException, DatatypeResolutionException) {

  CheckArgument(em != NULL, em, "cannot resolve a Datatype with a NULL expression manager");
  CheckArgument(!isResolved(),
                "cannot resolve a Datatype constructor twice; "
                "perhaps the same constructor was added twice, "
                "or to two datatypes?");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(*em);

  NodeManager* nm = NodeManager::fromExprManager(em);
  TypeNode selfTypeNode = TypeNode::fromType(self);
  size_t index = 0;
  for(std::vector<DatatypeConstructorArg>::iterator i = d_args.begin(), i_end = d_args.end(); i != i_end; ++i) {
    if((*i).d_selector.isNull()) {
      // the unresolved type wasn't created here; do name resolution
      string typeName = (*i).d_name.substr((*i).d_name.find('\0') + 1);
      (*i).d_name.resize((*i).d_name.find('\0'));
      if(typeName == "") {
        (*i).d_selector = nm->mkSkolem((*i).d_name, nm->mkSelectorType(selfTypeNode, selfTypeNode), "is a selector", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
      } else {
        map<string, DatatypeType>::const_iterator j = resolutions.find(typeName);
        if(j == resolutions.end()) {
          stringstream msg;
          msg << "cannot resolve type \"" << typeName << "\" "
              << "in selector \"" << (*i).d_name << "\" "
              << "of constructor \"" << d_name << "\"";
          throw DatatypeResolutionException(msg.str());
        } else {
          (*i).d_selector = nm->mkSkolem((*i).d_name, nm->mkSelectorType(selfTypeNode, TypeNode::fromType((*j).second)), "is a selector", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
        }
      }
    } else {
      // the type for the selector already exists; may need
      // complex-type substitution
      Type range = (*i).d_selector.getType();
      if(!placeholders.empty()) {
        range = range.substitute(placeholders, replacements);
      }
      if(!paramTypes.empty() ) {
        range = doParametricSubstitution( range, paramTypes, paramReplacements );
      }
      (*i).d_selector = nm->mkSkolem((*i).d_name, nm->mkSelectorType(selfTypeNode, TypeNode::fromType(range)), "is a selector", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
    }
    Node::fromExpr((*i).d_selector).setAttribute(DatatypeConsIndexAttr(), cindex);
    Node::fromExpr((*i).d_selector).setAttribute(DatatypeIndexAttr(), index++);
    (*i).d_resolved = true;
  }

  Assert(index == getNumArgs());

  // Set constructor/tester last, since DatatypeConstructor::isResolved()
  // returns true when d_tester is not the null Expr.  If something
  // fails above, we want Constuctor::isResolved() to remain "false".
  // Further, mkConstructorType() iterates over the selectors, so
  // should get the results of any resolutions we did above.
  d_tester = nm->mkSkolem(getTesterName(), nm->mkTesterType(selfTypeNode), "is a tester", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
  d_constructor = nm->mkSkolem(getName(), nm->mkConstructorType(*this, selfTypeNode), "is a constructor", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
  // associate constructor with all selectors
  for(std::vector<DatatypeConstructorArg>::iterator i = d_args.begin(), i_end = d_args.end(); i != i_end; ++i) {
    (*i).d_constructor = d_constructor;
  }
}

Type DatatypeConstructor::doParametricSubstitution( Type range,
                                  const std::vector< SortConstructorType >& paramTypes,
                                  const std::vector< DatatypeType >& paramReplacements ) {
  TypeNode typn = TypeNode::fromType( range );
  if(typn.getNumChildren() == 0) {
    return range;
  } else {
    std::vector< Type > origChildren;
    std::vector< Type > children;
    for(TypeNode::const_iterator i = typn.begin(), iend = typn.end();i != iend; ++i) {
      origChildren.push_back( (*i).toType() );
      children.push_back( doParametricSubstitution( (*i).toType(), paramTypes, paramReplacements ) );
    }
    for( unsigned i = 0; i < paramTypes.size(); ++i ) {
      if( paramTypes[i].getArity() == origChildren.size() ) {
        Type tn = paramTypes[i].instantiate( origChildren );
        if( range == tn ) {
          return paramReplacements[i].instantiate( children );
        }
      }
    }
    NodeBuilder<> nb(typn.getKind());
    for( unsigned i = 0; i < children.size(); ++i ) {
      nb << TypeNode::fromType( children[i] );
    }
    return nb.constructTypeNode().toType();
  }
}

DatatypeConstructor::DatatypeConstructor(std::string name) :
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the tester name away inside the constructor name until
  // resolution.
  d_name(name + '\0' + "is_" + name), // default tester name is "is_FOO"
  d_tester(),
  d_args() {
  CheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
}

DatatypeConstructor::DatatypeConstructor(std::string name, std::string tester) :
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the tester name away inside the constructor name until
  // resolution.
  d_name(name + '\0' + tester),
  d_tester(),
  d_args() {
  CheckArgument(name != "", name, "cannot construct a datatype constructor without a name");
  CheckArgument(!tester.empty(), tester, "cannot construct a datatype constructor without a tester");
}

void DatatypeConstructor::setSygus( Expr op, Expr let_body, std::vector< Expr >& let_args, unsigned num_let_input_args ){
  d_sygus_op = op;
  d_sygus_let_body = let_body;
  d_sygus_let_args.insert( d_sygus_let_args.end(), let_args.begin(), let_args.end() );
  d_sygus_num_let_input_args = num_let_input_args;
}


void DatatypeConstructor::addArg(std::string selectorName, Type selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away inside a var until resolution (when we can
  // create the proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  CheckArgument(!selectorType.isNull(), selectorType, "cannot add a null selector type");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(selectorType);

  Expr type = NodeManager::currentNM()->mkSkolem("unresolved_" + selectorName, TypeNode::fromType(selectorType), "is an unresolved selector type placeholder", NodeManager::SKOLEM_EXACT_NAME | NodeManager::SKOLEM_NO_NOTIFY).toExpr();
  Debug("datatypes") << type << endl;
  d_args.push_back(DatatypeConstructorArg(selectorName, type));
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeUnresolvedType selectorType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we stow
  // the selector type away after a NUL in the name string until
  // resolution (when we can create the proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  CheckArgument(selectorType.getName() != "", selectorType, "cannot add a null selector type");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0' + selectorType.getName(), Expr()));
}

void DatatypeConstructor::addArg(std::string selectorName, DatatypeSelfType) {
  // We don't want to introduce a new data member, because eventually
  // we're going to be a constant stuffed inside a node.  So we mark
  // the name string with a NUL to indicate that we have a
  // self-selecting selector until resolution (when we can create the
  // proper selector type)
  CheckArgument(!isResolved(), this, "cannot modify a finalized Datatype constructor");
  d_args.push_back(DatatypeConstructorArg(selectorName + '\0', Expr()));
}

std::string DatatypeConstructor::getName() const throw() {
  return d_name.substr(0, d_name.find('\0'));
}

std::string DatatypeConstructor::getTesterName() const throw() {
  return d_name.substr(d_name.find('\0') + 1);
}

Expr DatatypeConstructor::getConstructor() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_constructor;
}

Type DatatypeConstructor::getSpecializedConstructorType(Type returnType) const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  ExprManagerScope ems(d_constructor);
  const Datatype& dt = Datatype::datatypeOf(d_constructor);
  CheckArgument(dt.isParametric(), this, "this datatype constructor is not parametric");
  DatatypeType dtt = dt.getDatatypeType();
  Matcher m(dtt);
  m.doMatching( TypeNode::fromType(dtt), TypeNode::fromType(returnType) );
  vector<Type> subst;
  m.getMatches(subst);
  vector<Type> params = dt.getParameters();
  return d_constructor.getType().substitute(params, subst);
}

Expr DatatypeConstructor::getTester() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_tester;
}

Expr DatatypeConstructor::getSygusOp() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_op;
}

Expr DatatypeConstructor::getSygusLetBody() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_let_body;
}

unsigned DatatypeConstructor::getNumSygusLetArgs() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_let_args.size();
}

Expr DatatypeConstructor::getSygusLetArg( unsigned i ) const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_let_args[i];
} 

unsigned DatatypeConstructor::getNumSygusLetInputArgs() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_num_let_input_args;
}

bool DatatypeConstructor::isSygusIdFunc() const {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");
  return d_sygus_let_args.size()==1 && d_sygus_let_args[0]==d_sygus_let_body;
}
  
Cardinality DatatypeConstructor::getCardinality() const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");

  Cardinality c = 1;

  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    c *= SelectorType((*i).getSelector().getType()).getRangeType().getCardinality();
  }

  return c;
}

/** compute the cardinality of this datatype */
Cardinality DatatypeConstructor::computeCardinality( std::vector< Type >& processing ) const throw(IllegalArgumentException){
  Cardinality c = 1;
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type t = SelectorType((*i).getSelector().getType()).getRangeType();
    if( t.isDatatype() ){
      const Datatype& dt = ((DatatypeType)t).getDatatype();
      c *= dt.computeCardinality( processing );
    }else{
      c *= t.getCardinality();
    }
  }
  return c;
}

bool DatatypeConstructor::computeWellFounded( std::vector< Type >& processing ) const throw(IllegalArgumentException){
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type t = SelectorType((*i).getSelector().getType()).getRangeType();
    if( t.isDatatype() ){
      const Datatype& dt = ((DatatypeType)t).getDatatype();
      if( !dt.computeWellFounded( processing ) ){
        return false;
      }
    }
  }
  return true;
}


bool DatatypeConstructor::isFinite() const throw(IllegalArgumentException) {
  CheckArgument(isResolved(), this, "this datatype constructor is not yet resolved");

  // we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);

  TNode self = Node::fromExpr(d_constructor);

  // is this already in the cache ?
  if(self.getAttribute(DatatypeFiniteComputedAttr())) {
    return self.getAttribute(DatatypeFiniteAttr());
  }

  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    if(! SelectorType((*i).getSelector().getType()).getRangeType().getCardinality().isFinite()) {
      self.setAttribute(DatatypeFiniteComputedAttr(), true);
      self.setAttribute(DatatypeFiniteAttr(), false);
      return false;
    }
  }

  self.setAttribute(DatatypeFiniteComputedAttr(), true);
  self.setAttribute(DatatypeFiniteAttr(), true);
  return true;
}

Expr DatatypeConstructor::computeGroundTerm( Type t, std::vector< Type >& processing, std::map< Type, Expr >& gt ) const throw(IllegalArgumentException) {
// we're using some internals, so we have to set up this library context
  ExprManagerScope ems(d_constructor);

  std::vector<Expr> groundTerms;
  groundTerms.push_back(getConstructor());

  // for each selector, get a ground term
  std::vector< Type > instTypes;
  std::vector< Type > paramTypes;
  if( DatatypeType(t).isParametric() ){
    paramTypes = DatatypeType(t).getDatatype().getParameters();
    instTypes = DatatypeType(t).getParamTypes();
  }
  for(const_iterator i = begin(), i_end = end(); i != i_end; ++i) {
    Type selType = SelectorType((*i).getSelector().getType()).getRangeType();
    if( DatatypeType(t).isParametric() ){
      selType = selType.substitute( paramTypes, instTypes );
    }
    Expr arg;
    if( selType.isDatatype() ){
      std::map< Type, Expr >::iterator itgt = gt.find( selType );
      if( itgt != gt.end() ){
        arg = itgt->second;
      }else{
        const Datatype & dt = DatatypeType(selType).getDatatype();
        arg = dt.computeGroundTerm( selType, processing );
      }
    }else{
      arg = selType.mkGroundTerm();
    }
    if( arg.isNull() ){
      Debug("datatypes") << "...unable to construct arg of " << (*i).getName() << std::endl;
      return Expr();
    }else{
      Debug("datatypes") << "...constructed arg " << arg.getType() << std::endl;
      groundTerms.push_back(arg);
    }
  }

  Expr groundTerm = getConstructor().getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, groundTerms);
  if( groundTerm.getType()!=t ){
    Assert( Datatype::datatypeOf( d_constructor ).isParametric() );
    //type is ambiguous, must apply type ascription
    Debug("datatypes-gt") << "ambiguous type for " << groundTerm << ", ascribe to " << t << std::endl;
    groundTerms[0] = getConstructor().getExprManager()->mkExpr(kind::APPLY_TYPE_ASCRIPTION,
                       getConstructor().getExprManager()->mkConst(AscriptionType(getSpecializedConstructorType(t))),
                       groundTerms[0]);
    groundTerm = getConstructor().getExprManager()->mkExpr(kind::APPLY_CONSTRUCTOR, groundTerms);
  }
  return groundTerm;
}


const DatatypeConstructorArg& DatatypeConstructor::operator[](size_t index) const {
  CheckArgument(index < getNumArgs(), index, "index out of bounds");
  return d_args[index];
}

const DatatypeConstructorArg& DatatypeConstructor::operator[](std::string name) const {
  for(const_iterator i = begin(); i != end(); ++i) {
    if((*i).getName() == name) {
      return *i;
    }
  }
  CheckArgument(false, name, "No such arg `%s' of constructor `%s'", name.c_str(), d_name.c_str());
}

Expr DatatypeConstructor::getSelector(std::string name) const {
  return (*this)[name].getSelector();
}

bool DatatypeConstructor::involvesExternalType() const{
  for(const_iterator i = begin(); i != end(); ++i) {
    if(! SelectorType((*i).getSelector().getType()).getRangeType().isDatatype()) {
      return true;
    }
  }
  return false;
}

DatatypeConstructorArg::DatatypeConstructorArg(std::string name, Expr selector) :
  d_name(name),
  d_selector(selector),
  d_resolved(false) {
  CheckArgument(name != "", name, "cannot construct a datatype constructor arg without a name");
}

std::string DatatypeConstructorArg::getName() const throw() {
  string name = d_name;
  const size_t nul = name.find('\0');
  if(nul != string::npos) {
    name.resize(nul);
  }
  return name;
}

Expr DatatypeConstructorArg::getSelector() const {
  CheckArgument(isResolved(), this, "cannot get a selector for an unresolved datatype constructor");
  return d_selector;
}

Expr DatatypeConstructorArg::getConstructor() const {
  CheckArgument(isResolved(), this,
                "cannot get a associated constructor for argument of an unresolved datatype constructor");
  return d_constructor;
}

SelectorType DatatypeConstructorArg::getType() const {
  return getSelector().getType();
}

bool DatatypeConstructorArg::isUnresolvedSelf() const throw() {
  return d_selector.isNull() && d_name.size() == d_name.find('\0') + 1;
}

static const int s_printDatatypeNamesOnly = std::ios_base::xalloc();

std::string DatatypeConstructorArg::getTypeName() const {
  Type t;
  if(isResolved()) {
    t = SelectorType(d_selector.getType()).getRangeType();
  } else {
    if(d_selector.isNull()) {
      string typeName = d_name.substr(d_name.find('\0') + 1);
      return (typeName == "") ? "[self]" : typeName;
    } else {
      t = d_selector.getType();
    }
  }

  // Unfortunately, in the case of complex selector types, we can
  // enter nontrivial recursion here.  Make sure that doesn't happen.
  stringstream ss;
  ss << Expr::setlanguage(language::output::LANG_CVC4);
  ss.iword(s_printDatatypeNamesOnly) = 1;
  t.toStream(ss);
  return ss.str();
}

std::ostream& operator<<(std::ostream& os, const Datatype& dt) {
  // These datatype things are recursive!  Be very careful not to
  // print an infinite chain of them.
  long& printNameOnly = os.iword(s_printDatatypeNamesOnly);
  Debug("datatypes-output") << "printNameOnly is " << printNameOnly << std::endl;
  if(printNameOnly) {
    return os << dt.getName();
  }

  class Scope {
    long& d_ref;
    long d_oldValue;
  public:
    Scope(long& ref, long value) : d_ref(ref), d_oldValue(ref) { d_ref = value; }
    ~Scope() { d_ref = d_oldValue; }
  } scope(printNameOnly, 1);
  // when scope is destructed, the value pops back

  Debug("datatypes-output") << "printNameOnly is now " << printNameOnly << std::endl;

  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << "DATATYPE " << dt.getName();
  if(dt.isParametric()) {
    os << '[';
    for(size_t i = 0; i < dt.getNumParameters(); ++i) {
      if(i > 0) {
        os << ',';
      }
      os << dt.getParameter(i);
    }
    os << ']';
  }
  os << " =" << endl;
  Datatype::const_iterator i = dt.begin(), i_end = dt.end();
  if(i != i_end) {
    os << "  ";
    do {
      os << *i << endl;
      if(++i != i_end) {
        os << "| ";
      }
    } while(i != i_end);
  }
  os << "END;" << endl;

  return os;
}

std::ostream& operator<<(std::ostream& os, const DatatypeConstructor& ctor) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << ctor.getName();

  DatatypeConstructor::const_iterator i = ctor.begin(), i_end = ctor.end();
  if(i != i_end) {
    os << "(";
    do {
      os << *i;
      if(++i != i_end) {
        os << ", ";
      }
    } while(i != i_end);
    os << ")";
  }

  return os;
}

std::ostream& operator<<(std::ostream& os, const DatatypeConstructorArg& arg) {
  // can only output datatypes in the CVC4 native language
  Expr::setlanguage::Scope ls(os, language::output::LANG_CVC4);

  os << arg.getName() << ": " << arg.getTypeName();

  return os;
}

}/* CVC4 namespace */
