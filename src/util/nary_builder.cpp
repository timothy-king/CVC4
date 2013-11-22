
#include "util/nary_builder.h"
#include "expr/metakind.h"
using namespace std;

namespace CVC4 {
namespace util {

Node NaryBuilder::mkAssoc(Kind kind, const std::vector<Node>& children){
  if(children.size() == 0){
    return zeroArity(kind);
  }else if(children.size() == 1){
    return children[0];
  }else{
    const unsigned int max = kind::metakind::getUpperBoundForKind(kind);
    const unsigned int min = kind::metakind::getLowerBoundForKind(kind);

    Assert(min <= children.size());

    unsigned int numChildren = children.size();
    NodeManager* nm = NodeManager::currentNM();
    if( numChildren <= max ) {
      return nm->mkNode(kind,children);
    }

    typedef std::vector<Node>::const_iterator const_iterator;
    const_iterator it = children.begin() ;
    const_iterator end = children.end() ;

    /* The new top-level children and the children of each sub node */
    std::vector<Node> newChildren;
    std::vector<Node> subChildren;

    while( it != end && numChildren > max ) {
      /* Grab the next max children and make a node for them. */
      for(const_iterator next = it + max; it != next; ++it, --numChildren ) {
        subChildren.push_back(*it);
      }
      Node subNode = nm->mkNode(kind,subChildren);
      newChildren.push_back(subNode);
      subChildren.clear();
    }

    /* If there's children left, "top off" the Expr. */
    if(numChildren > 0) {
      /* If the leftovers are too few, just copy them into newChildren;
       * otherwise make a new sub-node  */
      if(numChildren < min) {
        for(; it != end; ++it) {
          newChildren.push_back(*it);
        }
      } else {
        for(; it != end; ++it) {
          subChildren.push_back(*it);
        }
        Node subNode = nm->mkNode(kind, subChildren);
        newChildren.push_back(subNode);
      }
    }

    /* It's inconceivable we could have enough children for this to fail
     * (more than 2^32, in most cases?). */
    AlwaysAssert( newChildren.size() <= max,
                  "Too many new children in mkAssociative" );

    /* It would be really weird if this happened (it would require
     * min > 2, for one thing), but let's make sure. */
    AlwaysAssert( newChildren.size() >= min,
                  "Too few new children in mkAssociative" );

    return nm->mkNode(kind,newChildren);
  }
}

Node NaryBuilder::zeroArity(Kind k){
  using namespace kind;
  NodeManager* nm = NodeManager::currentNM();
  switch(k){
  case AND:
    return nm->mkConst(true);
  case OR:
    return nm->mkConst(false);
  case PLUS:
    return nm->mkConst(Rational(0));
  case MULT:
    return nm->mkConst(Rational(1));
  default:
    return Node::null();
  }
}


}/* util namespace */
}/* CVC4 namespace */
