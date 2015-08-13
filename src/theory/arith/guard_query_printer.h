#pragma once

#include <iostream>
#include <vector>

#include "expr/node.h"
#include "util/result.h"


namespace CVC4 {
namespace theory {
namespace arith {


class AssertionPartition {
private:
  typedef std::vector<Node> NodeVec;
  
  NodeVec d_assertions;
  NodeVec::iterator d_pos;

public:
  AssertionPartition();
  AssertionPartition(const NodeVec& as, NodeVec::iterator p);
  
  size_t size_first() const;
  NodeVec::const_iterator begin_first() const;
  NodeVec::const_iterator end_first() const;

  size_t size_second() const;
  NodeVec::const_iterator begin_second() const;
  NodeVec::const_iterator end_second() const;

  size_t size() const;
  NodeVec::const_iterator begin() const;
  NodeVec::const_iterator end() const;
};

AssertionPartition partitionNonlinear(const std::vector<Node>& assertions);

void produceGuardedQuery(std::ostream& os, const AssertionPartition& partitioned);

std::pair<Result::Sat, Node> executeGuardedQuery(const AssertionPartition& partitioned);

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
