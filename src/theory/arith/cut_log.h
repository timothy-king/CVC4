
#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "util/statistics_registry.h"
#include "theory/arith/arithvar.h"
#include "util/dense_map.h"
#include <vector>
#include <map>
#include <set>


namespace CVC4 {
namespace theory {
namespace arith {


struct PrimitiveVec {
  int len;
  int* inds;
  double* coeffs;
  PrimitiveVec();
  ~PrimitiveVec();
  bool initialized() const;
  void clear();
  void setup(int l);
  void print(std::ostream& out) const;
};

enum CutInfoKlass{ MirCutKlass, GmiCutKlass, BranchCutKlass, UnknownKlass};
std::ostream& operator<<(std::ostream& os, CutInfoKlass kl);

class CutInfo {
public:
  int execOrd;

  CutInfoKlass klass;
  int ord;    /* cut's ordinal in the current node pool */
  Kind cut_type_;   /* Lowerbound, upperbound or undefined. */
  double cut_rhs; /* right hand side of the cut */
  PrimitiveVec cut_vec; /* vector of the cut */
  int M;     /* the number of rows at the time the cut was made.
             * this is required to descramble indices later*/
  int N;

  int row_id; /* if selected, make this non-zero */

  /* if the cut is successfully reproduced this is non-null */
  Node asLiteral;
  Node explanation;

  CutInfo(CutInfoKlass kl, int cutid, int ordinal);

  virtual ~CutInfo(){}

  void print(std::ostream& out) const;
  void init_cut(int l);

  int operator<(const CutInfo& o) const{
    return execOrd < o.execOrd;
  }
};

struct BranchCutInfo : public CutInfo {
  BranchCutInfo(int execOrd, int br,  Kind dir, double val);
};

class NodeLog {
private:
  int d_nid;
  struct CmpCutPointer{
    int operator()(const CutInfo* a, const CutInfo* b) const{
      return *a < *b;
    }
  };
  typedef std::set<CutInfo*, CmpCutPointer> CutSet;
  CutSet d_cuts;
  std::map<int, int> d_rowIdsSelected;

  enum Status {Open, Closed, Branched};
  Status stat;

  int br_var; // branching variable
  double br_val;
  int dn;
  int up;

public:
  NodeLog();
  NodeLog(int node);
  ~NodeLog();

  int getNodeId() const;
  void addSelected(int ord, int sel);
  void applySelected();
  void addCut(CutInfo* ci);
  void print(std::ostream& o) const;

  bool isBranch() const;
  int branchVariable() const;
  double branchValue() const;

  typedef CutSet::const_iterator const_iterator;
  const_iterator begin() const;
  const_iterator end() const;

  void setBranch(int br, double val, int dn, int up);
  void closeNode();

  int getDownId() const;
  int getUpId() const;
};

class ApproximateSimplex;
class TreeLog {
private:
  ApproximateSimplex* d_generator;

  int next_exec_ord;
  typedef std::map<int, NodeLog> ToNodeMap;
  ToNodeMap d_toNode;
  DenseMultiset d_branches;

  uint32_t d_numCuts;

  bool d_active;

public:
  TreeLog();

  NodeLog& getNode(int nid);
  void branch(int nid, int br, double val, int dn, int up);
  void close(int nid);

  void applySelected();
  void print(std::ostream& o) const;

  typedef ToNodeMap::const_iterator const_iterator;
  const_iterator begin() const;
  const_iterator end() const;

  int getExecutionOrd();
  void clear();

  void makeInactive();
  void makeActive();

  bool isActivelyLogging() const;

  void addCut();
  uint32_t cutCount() const;

  void logBranch(uint32_t x);
  uint32_t numBranches(uint32_t x);

  int getRootId() const;

  void printBranchInfo(std::ostream& os) const;
};

struct DenseVector {
  DenseMap<Rational> lhs;
  Rational rhs;
  void purge();
  void print(std::ostream& os) const;

  static void print(std::ostream& os, const DenseMap<Rational>& lhs);
};


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
