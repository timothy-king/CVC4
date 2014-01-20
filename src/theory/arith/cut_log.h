
#include "cvc4_private.h"

#pragma once

#include "expr/kind.h"
#include "util/statistics_registry.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/constraint_forward.h"
#include "util/dense_map.h"
#include <vector>
#include <map>
#include <set>


namespace CVC4 {
namespace theory {
namespace arith {

/** A low level vector of indexed doubles. */
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
std::ostream& operator<<(std::ostream& os, const PrimitiveVec& pv);

struct DenseVector {
  DenseMap<Rational> lhs;
  Rational rhs;
  void purge();
  void print(std::ostream& os) const;

  static void print(std::ostream& os, const DenseMap<Rational>& lhs);
};

/** The different kinds of cuts. */
enum CutInfoKlass{ MirCutKlass, GmiCutKlass, BranchCutKlass, UnknownKlass};
std::ostream& operator<<(std::ostream& os, CutInfoKlass kl);

/** A general class for describing a cut. */
class CutInfo {
protected:
  CutInfoKlass d_klass;
  int d_execOrd;

  int d_poolOrd;    /* cut's ordinal in the current node pool */
  Kind d_cutType;   /* Lowerbound, upperbound or undefined. */
  double d_cutRhs; /* right hand side of the cut */
  PrimitiveVec d_cutVec; /* vector of the cut */

  /**
   * The number of rows at the time the cut was made.
   * This is required to descramble indices after the fact!
   */
  int d_mAtCreation;

  /** This is the number of structural variables. */
  int d_N;

  /** if selected, make this non-zero */
  int d_rowId;

  /* If the cut has been successfully created,
   * the cut is stored in exact precision in d_exactPrecision.
   * If the cut has not yet been proven, this is null.
   */
  DenseVector* d_exactPrecision;

  ConstraintCPVec* d_explanation;

public:
  CutInfo(CutInfoKlass kl, int cutid, int ordinal);

  virtual ~CutInfo();

  int getId() const;

  int getRowId() const;
  void setRowId(int rid);

  void print(std::ostream& out) const;
  //void init_cut(int l);
  PrimitiveVec& getCutVector();
  const PrimitiveVec& getCutVector() const;

  Kind getKind() const;
  void setKind(Kind k);


  void setRhs(double r);
  double getRhs() const;

  CutInfoKlass getKlass() const;
  int poolOrdinal() const;

  void setDimensions(int N, int M);
  int getN() const;
  int getMAtCreation() const;

  bool operator<(const CutInfo& o) const;

  /* Returns true if the cut was successfully made in exact precision.*/
  bool success() const;

  /* Returns true if the cut has an explanation. */
  bool proven() const;

  void setCut(const DenseVector& ep);
  void setExplanation(const ConstraintCPVec& ex);
  void swapExplanation(ConstraintCPVec& ex);

  const DenseVector& getExactPrecision() const;
  const ConstraintCPVec& getExplanation() const;
};
std::ostream& operator<<(std::ostream& os, const CutInfo& ci);

struct BranchCutInfo : public CutInfo {
  BranchCutInfo(int execOrd, int br,  Kind dir, double val);
};

class TreeLog;

class NodeLog {
private:
  int d_nid;
  NodeLog* d_parent; /* If null this is the root */
  TreeLog* d_tl;     /* TreeLog containing the node. */

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
  NodeLog(); /* default constructor. */
  NodeLog(TreeLog* tl, int node); /* makes a root node. */
  NodeLog(TreeLog* tl, NodeLog* parent, int node);/* makes a non-root node. */

  ~NodeLog();

  int getNodeId() const;
  void addSelected(int ord, int sel);
  void applySelected();
  void addCut(CutInfo* ci);
  void print(std::ostream& o) const;

  bool isRoot() const;
  const NodeLog& getParent() const;

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



}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
