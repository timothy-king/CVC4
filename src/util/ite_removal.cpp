/*********************                                                        */
/*! \file ite_removal.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Andrew Reynolds, Morgan Deters
 ** Minor contributors (to current version): Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Removal of term ITEs
 **
 ** Removal of term ITEs.
 **/

#include <vector>

#include "util/ite_removal.h"
#include "expr/command.h"
#include "theory/quantifiers/options.h"

using namespace CVC4;
using namespace std;

namespace CVC4 {

void RemoveITE::run(std::vector<Node>& output, IteSkolemMap& iteSkolemMap)
{
  for (unsigned i = 0, i_end = output.size(); i < i_end; ++ i) {
    std::vector<Node> quantVar;
    // Do this in two steps to avoid Node problems(?)
    // Appears related to bug 512, splitting this into two lines
    // fixes the bug on clang on Mac OS
    Node itesRemoved = run(output[i], output, iteSkolemMap, quantVar);
    output[i] = itesRemoved;
  }
}

Node RemoveITE::run(TNode node, std::vector<Node>& output,
                    IteSkolemMap& iteSkolemMap, std::vector<Node>& quantVar) {
  // Current node
  Debug("ite") << "removeITEs(" << node << ")" << endl;

  // The result may be cached already
  NodeManager *nodeManager = NodeManager::currentNM();
  ITECache::const_iterator i = d_iteCache.find(node);
  if(i != d_iteCache.end()) {
    Node cached = (*i).second;
    Debug("ite") << "removeITEs: in-cache: " << cached << endl;
    return cached.isNull() ? Node(node) : cached;
  }

  // If an ITE replace it
  if(node.getKind() == kind::ITE) {
    TypeNode nodeType = node.getType();
    if(!nodeType.isBoolean()) {
      Node skolem;
      // Make the skolem to represent the ITE
      if( quantVar.empty() ){
        skolem = nodeManager->mkSkolem("termITE_$$", nodeType, "a variable introduced due to term-level ITE removal");
      }else{
        //if in the scope of free variables, make a skolem operator
        vector< TypeNode > argTypes;
        for( size_t i=0; i<quantVar.size(); i++ ){
          argTypes.push_back( quantVar[i].getType() );
        }
        TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, nodeType );
        Node op = NodeManager::currentNM()->mkSkolem( "termITEop_$$", typ, "a function variable introduced due to term-level ITE removal" );
        vector< Node > funcArgs;
        funcArgs.push_back( op );
        funcArgs.insert( funcArgs.end(), quantVar.begin(), quantVar.end() );
        skolem = NodeManager::currentNM()->mkNode( kind::APPLY_UF, funcArgs );
      }

      // The new assertion
      Node newAssertion =
        nodeManager->mkNode(kind::ITE, node[0], skolem.eqNode(node[1]),
                            skolem.eqNode(node[2]));
      Debug("ite") << "removeITEs(" << node << ") => " << newAssertion << endl;

      // Attach the skolem
      d_iteCache.insert(node, skolem);

      // Remove ITEs from the new assertion, rewrite it and push it to the output
      newAssertion = run(newAssertion, output, iteSkolemMap, quantVar);

      if( !quantVar.empty() ){
        //if in the scope of free variables, it is a quantified assertion
        vector< Node > children;
        children.push_back( NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, quantVar ) );
        children.push_back( newAssertion );
        newAssertion = NodeManager::currentNM()->mkNode( kind::FORALL, children );
      }

      iteSkolemMap[skolem] = output.size();
      output.push_back(newAssertion);

      // The representation is now the skolem
      return skolem;
    }
  }

  // If not an ITE, go deep
  if( ( node.getKind() != kind::FORALL || options::iteRemoveQuant() ) &&
      node.getKind() != kind::EXISTS &&
      node.getKind() != kind::REWRITE_RULE ) {
    std::vector< Node > newQuantVar;
    newQuantVar.insert( newQuantVar.end(), quantVar.begin(), quantVar.end() );
    if( node.getKind()==kind::FORALL ){
      for( size_t i=0; i<node[0].getNumChildren(); i++ ){
        newQuantVar.push_back( node[0][i] );
      }
    }
    // Switches to using a 2 state automaton
    if(options::lazyITEConstruction()){
      // Search for the first modified position
      // If there is no modified child, node return Node::null().
      // If there is a modified child,
      // push back the unmodified parts and begin constructing the modified node
      Node newChild = Node::null();
      TNode::const_iterator first_modified_pos = node.begin();
      TNode::const_iterator end = node.end();
      for(; first_modified_pos != end; ++first_modified_pos) {
        newChild = run(*first_modified_pos, output, iteSkolemMap, newQuantVar);
        if(newChild != *first_modified_pos){
          break;
        }
      }
      if(first_modified_pos == end){ // nothing was modified
        d_iteCache.insert(node, Node::null());
        return node;
      }else{
        // Something was modified
        // Start constructing the new node now
        NodeBuilder<> newChildren(nodeManager, node.getKind());
        if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
          newChildren << (node.getOperator());
        }
        TNode::const_iterator it = node.begin();
        // Push back the untouched prefix
        for(; it != first_modified_pos; ++it) {
          newChildren << (*it);
        }
        Assert(it == first_modified_pos);
        // Push_back the first modified child
        newChildren << newChild;
        // move the iterator past first_modified_pos
        ++it;
        for(; it != end; ++it){
          newChild = run(*it, output, iteSkolemMap, newQuantVar);
          newChildren << newChild;
        }
        Node cached = (Node)newChildren;
        d_iteCache.insert(node, cached);
        return cached;
      }
    }else{ // older implementation
      vector<Node> newChildren;
      bool somethingChanged = false;
      if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
        newChildren.push_back(node.getOperator());
      }
      // Remove the ITEs from the children
      for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
        Node newChild = run(*it, output, iteSkolemMap, newQuantVar);
        somethingChanged |= (newChild != *it);
        newChildren.push_back(newChild);
      }

      // If changes, we rewrite
      if(somethingChanged) {
        Node cached = nodeManager->mkNode(node.getKind(), newChildren);
        d_iteCache.insert(node, cached);
        return cached;
      } else {
        d_iteCache.insert(node, Node::null());
        return node;
      }
    }
  } else {
    d_iteCache.insert(node, Node::null());
    return node;
  }
}


void RemoveITE::containsNoTermItes(Node n)
{
  d_iteCache.insert_safe(n, Node::null());
}

}/* CVC4 namespace */
