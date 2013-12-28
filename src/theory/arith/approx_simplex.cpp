#include "cvc4autoconfig.h"

#include "theory/arith/approx_simplex.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/constraint.h"
#include <math.h>
#include <cmath>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

struct PrimitiveVec {
  int len;
  int* inds;
  double* coeffs;
  PrimitiveVec()
    : len(0)
    , inds(NULL)
    , coeffs(NULL)
  {}

  ~PrimitiveVec(){
    clear();
  }

  bool initialized() const { return inds != NULL; }
  void clear() {
    if(initialized()){
      delete[] inds;
      delete[] coeffs;
      len = 0;
      inds = NULL;
      coeffs = NULL;      
    }
  }
  void setup(int l){
    Assert(!initialized());
    len = l;
    inds = new int[1+len];
    coeffs = new double[1+len];
  }
  void print(std::ostream& out){
    Assert(initialized());
    out << len << " ";
    for(int i = 1; i <= len; ++i){
      out << "["<< inds[i] <<", " << coeffs[i]<<"]";
    }
    out << endl;
  }
};

enum CutInfoKlass{ MirCutKlass, GmiCutKlass, UnknownKlass};

class CutInfo {
public:
  CutInfoKlass klass;
  int ord;    /* cut's orderinal in the current node pool */
  int cut_type;   /* Lowerbound or upperbound. */
  double cut_rhs; /* right hand side of the cut */
  PrimitiveVec cut_vec; /* vector of the cut */
  CutInfo(CutInfoKlass kl, int o)
    : klass(kl)
    , ord(o)
    , cut_type(-1)
    , cut_rhs()
    , cut_vec()
  {}

  virtual ~CutInfo(){}
    
  void print(ostream& out){
    out << ord << " " << cut_type << " " << cut_rhs << endl;
    cut_vec.print(out);
  }
  void init_cut(int l){
    cut_vec.setup(l);
  }
};

class CutsOnNode{
private:
  int d_nid;
  std::vector<CutInfo*> d_cuts;
  std::set<int> d_selected;

  void shrinkCuts(size_t n){
    Assert(n <= d_cuts.size());
    while(d_cuts.size() > n){
      CutInfo* cut = d_cuts.back();
      d_cuts.pop_back();
      delete cut;
    }
    Assert(d_cuts.size() == n);
  }

public:
  CutsOnNode()
    : d_nid(-1)
    , d_cuts()
    , d_selected()
  {}

  CutsOnNode(int node)
    : d_nid(node)
    , d_cuts()
    , d_selected()
  {}

  ~CutsOnNode(){
    shrinkCuts(0);
    Assert(d_cuts.empty());
  }

  int getNodeId() const { return d_nid; }

  void addSelected(int ord){
    d_selected.insert(ord);
  }

  void addSelected(int n, const int* ords){
    for(int i = 1; i <= n; ++i){
      addSelected(ords[i]);
    }
  }

  void applySelected() {
    size_t iter, newEnd;
    for(iter = 0, newEnd = d_cuts.size(); iter < newEnd; ++iter){
      CutInfo* curr = d_cuts[iter];
      if(d_selected.find(curr->ord) == d_selected.end()){// drop
        --newEnd;
        std::swap(d_cuts[iter], d_cuts[newEnd]);
      }
    }
    shrinkCuts(newEnd);
  }

  void addCut(CutInfo* ci){
    Assert(ci != NULL);
    d_cuts.push_back(ci);
  }
};

class TreeLog {
  std::map<int, CutsOnNode> d_toNode;

public:
  void addCut(int nid, CutInfo* ci){
    if(d_toNode.find(nid) == d_toNode.end()){
      d_toNode.insert(make_pair(nid, CutsOnNode(nid) ));
    }
    CutsOnNode& node = d_toNode[nid];
    node.addCut(ci);
  }

  void addSelected(int nid, int ord){
    Assert(d_toNode.find(nid) != d_toNode.end());
    
    CutsOnNode& node = d_toNode[nid];
    node.addSelected(ord);
  }
};

struct AuxInfo {
  TreeLog tl;
  int pivotLimit;
};
  
ApproximateSimplex::ApproximateSimplex() :
  d_pivotLimit(std::numeric_limits<int>::max())
{}

void ApproximateSimplex::setPivotLimit(int pivotLimit){
  Assert(pivotLimit >= 0);
  d_pivotLimit = pivotLimit;
}

const double ApproximateSimplex::SMALL_FIXED_DELTA = .000000001;
const double ApproximateSimplex::TOLERENCE = 1 + .000000001;

bool ApproximateSimplex::roughlyEqual(double a, double b){
  if (a == 0){
    return -SMALL_FIXED_DELTA <= b && b <= SMALL_FIXED_DELTA;
  }else if (b == 0){
    return -SMALL_FIXED_DELTA <= a && a <= SMALL_FIXED_DELTA;
  }else{
    return std::abs(b/a) <= TOLERENCE && std::abs(a/b) <= TOLERENCE;
  }
}

Rational ApproximateSimplex::cfeToRational(const vector<Integer>& exp){
  if(exp.empty()){
    return Rational(0);
  }else{
    Rational result = exp.back();
    vector<Integer>::const_reverse_iterator exp_iter = exp.rbegin();
    vector<Integer>::const_reverse_iterator exp_end = exp.rend();
    ++exp_iter;
    while(exp_iter != exp_end){
      result = result.inverse();
      const Integer& i = *exp_iter;
      result += i;
      ++exp_iter;
    }
    return result;
  }
}
std::vector<Integer> ApproximateSimplex::rationalToCfe(const Rational& q, int depth){
  vector<Integer> mods;
  if(!q.isZero()){
    Rational carry = q;
    for(int i = 0; i <= depth; ++i){
      Assert(!carry.isZero());
      mods.push_back(Integer());
      Integer& back = mods.back();
      back = carry.floor();
      //cout << "  cfe["<<i<<"]: " << back << endl;
      carry -= back;
      if(carry.isZero()){
        break;
      }else if(ApproximateSimplex::roughlyEqual(carry.getDouble(), 0.0)){
        break;
      }else{
        carry = carry.inverse();
      }
    }
  }
  return mods;
}

Rational ApproximateSimplex::estimateWithCFE(const Rational& q, int depth){
  std::vector<Integer> cfe = rationalToCfe(q,depth);
  return cfeToRational(cfe);
}

Rational ApproximateSimplex::estimateWithCFE(double d){
  return estimateWithCFE(Rational::fromDouble(d), 10);
}

class ApproxNoOp : public ApproximateSimplex {
public:
  ApproxNoOp(const ArithVariables& vars){}
  ~ApproxNoOp(){}

  virtual ApproxResult solveRelaxation(){
    return ApproxError;
  }
  virtual Solution extractRelaxation() const{
    return Solution();
  }

  virtual ArithRatPairVec heuristicOptCoeffs() const{
    return ArithRatPairVec();
  }

  virtual ApproxResult solveMIP(){
    return ApproxError;
  }
  virtual Solution extractMIP() const{
    return Solution();
  }

  virtual void setOptCoeffs(const ArithRatPairVec& ref){}
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

/* Begin the declaration of GLPK specific code. */
#ifdef CVC4_USE_GLPK
extern "C" {
/* Sometimes the header is in a subdirectory glpk/, sometimes not.
 * The configure script figures it out. */
#ifdef HAVE_GLPK_GLPK_H
#  include <glpk/glpk.h>
#else /* HAVE_GLPK_GLPK_H */
#  include <glpk.h>
#endif /* HAVE_GLPK_GLPK_H */
}/* extern "C" */

namespace CVC4 {
namespace theory {
namespace arith {

class ApproxGLPK : public ApproximateSimplex {
private:
  glp_prob* d_prob;
  const ArithVariables& d_vars;

  DenseMap<int> d_colIndices;
  DenseMap<int> d_rowIndices;


  int d_instanceID;

  bool d_solvedRelaxation;
  bool d_solvedMIP;

  static int s_verbosity;

public:
  ApproxGLPK(const ArithVariables& vars);
  ~ApproxGLPK();

  virtual ApproxResult solveRelaxation();
  virtual Solution extractRelaxation() const{
    return extractSolution(false);
  }

  virtual ArithRatPairVec heuristicOptCoeffs() const;

  virtual ApproxResult solveMIP();
  virtual Solution extractMIP() const{
    return extractSolution(true);
  }
  virtual void setOptCoeffs(const ArithRatPairVec& ref);

  static void printGLPKStatus(int status, std::ostream& out);
private:
  Solution extractSolution(bool mip) const;
  int guessDir(ArithVar v) const;
};

int ApproxGLPK::s_verbosity = 1;

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
#endif /*#ifdef CVC4_USE_GLPK */
/* End the declaration of GLPK specific code. */

/* Begin GPLK/NOGLPK Glue code. */
namespace CVC4 {
namespace theory {
namespace arith {
ApproximateSimplex* ApproximateSimplex::mkApproximateSimplexSolver(const ArithVariables& vars){
#ifdef CVC4_USE_GLPK
  return new ApproxGLPK(vars);
#else
  return new ApproxNoOp(vars);
#endif
}
bool ApproximateSimplex::enabled() {
#ifdef CVC4_USE_GLPK
  return true;
#else
  return false;
#endif
}
}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
/* End GPLK/NOGLPK Glue code. */


/* Begin GPLK implementation. */
#ifdef CVC4_USE_GLPK
namespace CVC4 {
namespace theory {
namespace arith {

static CutInfoKlass fromGlpkClass(int klass){
  switch(klass){
  case GLP_RF_GMI: return GmiCutKlass;
  case GLP_RF_MIR: return MirCutKlass;
  case GLP_RF_COV:
  case GLP_RF_CLQ:
  default:         return UnknownKlass;
  }
}

ApproxGLPK::ApproxGLPK(const ArithVariables& avars) :
  d_vars(avars), d_solvedRelaxation(false), d_solvedMIP(false)
{
  static int instance = 0;
  ++instance;
  d_instanceID = instance;

  d_prob = glp_create_prob();
  glp_set_obj_dir(d_prob, GLP_MAX);
  glp_set_prob_name(d_prob, "ApproximateSimplex::approximateFindModel");

  int numRows = 0;
  int numCols = 0;

  // Assign each variable to a row and column variable as it appears in the input
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    if(d_vars.isSlack(v)){
      ++numRows;
      d_rowIndices.set(v, numRows);
    }else{
      ++numCols;
      d_colIndices.set(v, numCols);
    }
  }
  glp_add_rows(d_prob, numRows);
  glp_add_cols(d_prob, numCols);

  // Assign the upper/lower bounds and types to each variable
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    if(s_verbosity >= 2){
      Message() << v  << " ";
      d_vars.printModel(v, Message());
    }

    int type;
    double lb = 0.0;
    double ub = 0.0;
    if(d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      if(d_vars.boundsAreEqual(v)){
        type = GLP_FX;
      }else{
        type = GLP_DB;
      }
      lb = d_vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
      ub = d_vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
    }else if(d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
      type = GLP_UP;
      ub = d_vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
    }else if(!d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      type = GLP_LO;
      lb = d_vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
    }else{
      type = GLP_FR;
    }

    if(d_vars.isSlack(v)){
      int rowIndex = d_rowIndices[v];
      glp_set_row_bnds(d_prob, rowIndex, type, lb, ub);
    }else{
      int colIndex = d_colIndices[v];
      int kind = d_vars.isInteger(v) ? GLP_IV : GLP_CV;
      glp_set_col_kind(d_prob, colIndex, kind);
      glp_set_col_bnds(d_prob, colIndex, type, lb, ub);
    }
  }

  // Count the number of entries
  int numEntries = 0;
  for(DenseMap<int>::const_iterator i = d_rowIndices.begin(), i_end = d_rowIndices.end(); i != i_end; ++i){
    ArithVar v = *i;
    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
    for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
      ++numEntries;
    }
  }

  int* ia = new int[numEntries+1];
  int* ja = new int[numEntries+1];
  double* ar = new double[numEntries+1];

  int entryCounter = 0;
  for(DenseMap<int>::const_iterator i = d_rowIndices.begin(), i_end = d_rowIndices.end(); i != i_end; ++i){
    ArithVar v = *i;
    int rowIndex = d_rowIndices[v];

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));

    for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){

      const Monomial& mono = *i;
      const Constant& constant = mono.getConstant();
      const VarList& variable = mono.getVarList();

      Node n = variable.getNode();

      Assert(d_vars.hasArithVar(n));
      ArithVar av = d_vars.asArithVar(n);
      int colIndex = d_colIndices[av];
      double coeff = constant.getValue().getDouble();

      ++entryCounter;
      ia[entryCounter] = rowIndex;
      ja[entryCounter] = colIndex;
      ar[entryCounter] = coeff;
    }
  }
  glp_load_matrix(d_prob, numEntries, ia, ja, ar);

  delete[] ia;
  delete[] ja;
  delete[] ar;
}
int ApproxGLPK::guessDir(ArithVar v) const{
  if(d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
    return -1;
  }else if(!d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
    return 1;
  }else if(!d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
    return 0;
  }else{
    int ubSgn = d_vars.getUpperBound(v).sgn();
    int lbSgn = d_vars.getLowerBound(v).sgn();

    if(ubSgn != 0 && lbSgn == 0){
      return -1;
    }else if(ubSgn == 0 && lbSgn != 0){
      return 1;
    }

    return 1;
  }
}

ArithRatPairVec ApproxGLPK::heuristicOptCoeffs() const{
  ArithRatPairVec ret;

  // Strategies are guess:
  // 1 simple shared "ceiling" variable: danoint, pk1
  //  x1 >= c, x1 >= tmp1, x1 >= tmp2, ...
  // 1 large row: fixnet, vpm2, pp08a
  //  (+ .......... ) <= c
  // Not yet supported:
  // 1 complex shared "ceiling" variable: opt1217
  //  x1 >= c, x1 >= (+ ..... ), x1 >= (+ ..... )
  //  and all of the ... are the same sign


  // Candidates:
  // 1) Upper and lower bounds are not equal.
  // 2) The variable is not integer
  // 3a) For columns look for a ceiling variable
  // 3B) For rows look for a large row with

  DenseMap<BoundCounts> d_colCandidates;
  DenseMap<uint32_t> d_rowCandidates;

  double sumRowLength = 0.0;
  uint32_t maxRowLength = 0;
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    if(s_verbosity >= 2){
      Message() << v  << " ";
      d_vars.printModel(v, Message());
    }

    int type;
    if(d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      if(d_vars.boundsAreEqual(v)){
        type = GLP_FX;
      }else{
        type = GLP_DB;
      }
    }else if(d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
      type = GLP_UP;
    }else if(!d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      type = GLP_LO;
    }else{
      type = GLP_FR;
    }

    if(type != GLP_FX && type != GLP_FR){

      if(d_vars.isSlack(v)){
        Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
        uint32_t len = p.size();
        d_rowCandidates.set(v, len);
        sumRowLength += len;
        maxRowLength =std::max(maxRowLength, len);
      }else if(!d_vars.isInteger(v)){
        d_colCandidates.set(v, BoundCounts());
      }
    }
  }

  uint32_t maxCount = 0;
  for(DenseMap<int>::const_iterator i = d_rowIndices.begin(), i_end = d_rowIndices.end(); i != i_end; ++i){
    ArithVar v = *i;

    bool lbCap = d_vars.hasLowerBound(v) && !d_vars.hasUpperBound(v);
    bool ubCap = !d_vars.hasLowerBound(v) && d_vars.hasUpperBound(v);

    if(lbCap || ubCap){
      Constraint b = lbCap ? d_vars.getLowerBoundConstraint(v)
        : d_vars.getUpperBoundConstraint(v);

      if(!(b->getValue()).noninfinitesimalIsZero()){ continue; }

      Polynomial poly = Polynomial::parsePolynomial(d_vars.asNode(v));
      if(poly.size() != 2) { continue; }

      Polynomial::iterator j = poly.begin();
      Monomial first = *j;
      ++j;
      Monomial second = *j;

      bool firstIsPos = first.constantIsPositive();
      bool secondIsPos = second.constantIsPositive();

      if(firstIsPos == secondIsPos){ continue; }

      Monomial pos = firstIsPos == lbCap ? first : second;
      Monomial neg = firstIsPos != lbCap ? first : second;
      // pos >= neg
      VarList p = pos.getVarList();
      VarList n = neg.getVarList();
      if(d_vars.hasArithVar(p.getNode())){
        ArithVar ap = d_vars.asArithVar(p.getNode());
        if( d_colCandidates.isKey(ap)){
          BoundCounts bc = d_colCandidates.get(ap);
          bc = BoundCounts(bc.lowerBoundCount(), bc.upperBoundCount()+1);
          maxCount = std::max(maxCount, bc.upperBoundCount());
          d_colCandidates.set(ap, bc);
        }
      }
      if(d_vars.hasArithVar(n.getNode())){
        ArithVar an = d_vars.asArithVar(n.getNode());
        if( d_colCandidates.isKey(an)){
          BoundCounts bc = d_colCandidates.get(an);
          bc = BoundCounts(bc.lowerBoundCount()+1, bc.upperBoundCount());
          maxCount = std::max(maxCount, bc.lowerBoundCount());
          d_colCandidates.set(an, bc);
        }
      }
    }
  }

  // Attempt row
  double avgRowLength = d_rowCandidates.size() >= 1 ?
    ( sumRowLength / d_rowCandidates.size() ) : 0.0;

  // There is a large row among the candidates
  bool guessARowCandidate = maxRowLength >= (10.0 * avgRowLength);

  double rowLengthReq = (maxRowLength * .9);

  if(guessARowCandidate){
    for(DenseMap<uint32_t>::const_iterator i = d_rowCandidates.begin(), iend =d_rowCandidates.end(); i != iend; ++i ){
      ArithVar r = *i;
      uint32_t len = d_rowCandidates[r];

      int dir = guessDir(r);
      if(len >= rowLengthReq){
        if(s_verbosity >= 1){
          Message() << "high row " << r << " " << len << " " << avgRowLength << " " << dir<< endl;
          d_vars.printModel(r, Message());
        }
        ret.push_back(ArithRatPair(r, Rational(dir)));
      }
    }
  }

  // Attempt columns
  bool guessAColCandidate = maxCount >= 4;
  if(guessAColCandidate){
    for(DenseMap<BoundCounts>::const_iterator i = d_colCandidates.begin(), iend = d_colCandidates.end(); i != iend; ++i ){
      ArithVar c = *i;
      BoundCounts bc = d_colCandidates[c];

      int dir = guessDir(c);
      double ubScore = double(bc.upperBoundCount()) / maxCount;
      double lbScore = double(bc.lowerBoundCount()) / maxCount;
      if(ubScore  >= .9 || lbScore >= .9){
        if(s_verbosity >= 1){
          Message() << "high col " << c << " " << bc << " " << ubScore << " " << lbScore << " " << dir << endl;
          d_vars.printModel(c, Message());
        }
        ret.push_back(ArithRatPair(c, Rational(c)));
      }
    }
  }


  return ret;
}

void ApproxGLPK::setOptCoeffs(const ArithRatPairVec& ref){
  DenseMap<double> nbCoeffs;

  for(ArithRatPairVec::const_iterator i = ref.begin(), iend = ref.end(); i != iend; ++i){
    ArithVar v = (*i).first;
    const Rational& q = (*i).second;

    if(d_vars.isSlack(v)){
      // replace the variable by its definition and multiply by q
      Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
      Polynomial pq = p * q;

      for(Polynomial::iterator j = pq.begin(), jend = pq.end(); j != jend; ++j){
        const Monomial& mono = *j;
        const Constant& constant = mono.getConstant();
        const VarList& variable = mono.getVarList();

        Node n = variable.getNode();

        Assert(d_vars.hasArithVar(n));
        ArithVar av = d_vars.asArithVar(n);
        int colIndex = d_colIndices[av];
        double coeff = constant.getValue().getDouble();
        if(!nbCoeffs.isKey(colIndex)){
          nbCoeffs.set(colIndex, 0.0);
        }
        nbCoeffs.set(colIndex, nbCoeffs[colIndex]+coeff);
      }
    }else{
      int colIndex = d_colIndices[v];
      double coeff = q.getDouble();
      if(!nbCoeffs.isKey(colIndex)){
        nbCoeffs.set(colIndex, 0.0);
      }
      nbCoeffs.set(colIndex, nbCoeffs[colIndex]+coeff);
    }
  }
  for(DenseMap<double>::const_iterator ci =nbCoeffs.begin(), ciend = nbCoeffs.end(); ci != ciend; ++ci){
    Index colIndex = *ci;
    double coeff = nbCoeffs[colIndex];
    glp_set_obj_coef(d_prob, colIndex, coeff);
  }
}


/*
 * rough strategy:
 *  real relaxation
 *   try approximate real optimization of error function
 *   pivot in its basis
 *   update to its assignment
 *   check with FCSimplex
 *  check integer solution
 *   try approximate mixed integer problem
 *   stop at the first feasible point
 *   pivot in its basis
 *   update to its assignment
 *   check with FCSimplex
 */

void ApproxGLPK::printGLPKStatus(int status, std::ostream& out){
  switch(status){
  case GLP_OPT:
    out << "GLP_OPT" << endl;
    break;
  case GLP_FEAS:
    out << "GLP_FEAS" << endl;
    break;
  case GLP_INFEAS:
    out << "GLP_INFEAS" << endl;
    break;
  case GLP_NOFEAS:
    out << "GLP_NOFEAS" << endl;
    break;
  case GLP_UNBND:
    out << "GLP_UNBND" << endl;
    break;
  case GLP_UNDEF:
    out << "GLP_UNDEF" << endl;
    break;
  default:
    out << "Status unknown" << endl;
    break;
  }
}

ApproxGLPK::~ApproxGLPK(){
  glp_delete_prob(d_prob);
}


ApproximateSimplex::Solution ApproxGLPK::extractSolution(bool mip) const{
  Assert(d_solvedRelaxation);
  Assert(!mip  || d_solvedMIP);

  ApproximateSimplex::Solution sol;
  DenseSet& newBasis = sol.newBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;

  for(ArithVariables::var_iterator i = d_vars.var_begin(), i_end = d_vars.var_end(); i != i_end; ++i){
    ArithVar vi = *i;
    bool isSlack = d_vars.isSlack(vi);
    int glpk_index = isSlack ? d_rowIndices[vi] : d_colIndices[vi];

    int status = isSlack ? glp_get_row_stat(d_prob, glpk_index) : glp_get_col_stat(d_prob, glpk_index);
    if(s_verbosity >= 2){
      Message() << "assignment " << vi << endl;
    }

    bool useDefaultAssignment = false;

    switch(status){
    case GLP_BS:
      //Message() << "basic" << endl;
      newBasis.add(vi);
      useDefaultAssignment = true;
      break;
    case GLP_NL:
    case GLP_NS:
      if(!mip){
        if(s_verbosity >= 2){ Message() << "non-basic lb" << endl; }
        newValues.set(vi, d_vars.getLowerBound(vi));
      }else{// intentionally fall through otherwise
        useDefaultAssignment = true;
      }
      break;
    case GLP_NU:
      if(!mip){
        if(s_verbosity >= 2){ Message() << "non-basic ub" << endl; }
        newValues.set(vi, d_vars.getUpperBound(vi));
      }else {// intentionally fall through otherwise
        useDefaultAssignment = true;
      }
      break;
    default:
      {
        useDefaultAssignment = true;
      }
      break;
    }

    if(useDefaultAssignment){
      if(s_verbosity >= 2){ Message() << "non-basic other" << endl; }

      double newAssign =
        mip ?
        (isSlack ? glp_mip_row_val(d_prob, glpk_index) :  glp_mip_col_val(d_prob, glpk_index))
        : (isSlack ? glp_get_row_prim(d_prob, glpk_index) :  glp_get_col_prim(d_prob, glpk_index));
      const DeltaRational& oldAssign = d_vars.getAssignment(vi);


      if(d_vars.hasLowerBound(vi) &&
         roughlyEqual(newAssign, d_vars.getLowerBound(vi).approx(SMALL_FIXED_DELTA))){
        //Message() << "  to lb" << endl;

        newValues.set(vi, d_vars.getLowerBound(vi));
      }else if(d_vars.hasUpperBound(vi) &&
               roughlyEqual(newAssign, d_vars.getUpperBound(vi).approx(SMALL_FIXED_DELTA))){
        newValues.set(vi, d_vars.getUpperBound(vi));
        // Message() << "  to ub" << endl;
      }else{

        double rounded = round(newAssign);
        if(roughlyEqual(newAssign, rounded)){
          // Message() << "roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
          newAssign = rounded;
        }else{
          // Message() << "not roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
        }

        DeltaRational proposal = estimateWithCFE(newAssign);


        if(roughlyEqual(newAssign, oldAssign.approx(SMALL_FIXED_DELTA))){
          // Message() << "  to prev value" << newAssign << " " << oldAssign << endl;
          proposal = d_vars.getAssignment(vi);
        }


        if(d_vars.strictlyLessThanLowerBound(vi, proposal)){
          //Message() << "  round to lb " << d_vars.getLowerBound(vi) << endl;
          proposal = d_vars.getLowerBound(vi);
        }else if(d_vars.strictlyGreaterThanUpperBound(vi, proposal)){
          //Message() << "  round to ub " << d_vars.getUpperBound(vi) << endl;
          proposal = d_vars.getUpperBound(vi);
        }else{
          //Message() << "  use proposal" << proposal << " " << oldAssign  << endl;
        }
        newValues.set(vi, proposal);
      }
    }
  }
  return sol;
}

ApproximateSimplex::ApproxResult ApproxGLPK::solveRelaxation(){
  Assert(!d_solvedRelaxation);

  glp_smcp parm;
  glp_init_smcp(&parm);
  parm.presolve = GLP_OFF;
  parm.meth = GLP_PRIMAL;
  parm.pricing = GLP_PT_PSE;
  parm.it_lim = d_pivotLimit;
  parm.msg_lev = GLP_MSG_OFF;
  if(s_verbosity >= 1){
    parm.msg_lev = GLP_MSG_ALL;
  }

  int res = glp_simplex(d_prob, &parm);
  switch(res){
  case 0:
    {
      int status = glp_get_status(d_prob);
      switch(status){
      case GLP_OPT:
      case GLP_FEAS:
      case GLP_UNBND:
        d_solvedRelaxation = true;
        return ApproxSat;
      case GLP_INFEAS:
      case GLP_NOFEAS:
        d_solvedRelaxation = true;
        return ApproxUnsat;
      default:
        return ApproxError;
      }
    }
  default:
    return ApproxError;
  }
}




struct MirInfo : public CutInfo {

  /** a sum of input rows. */
  PrimitiveVec row_sum;  

  int n;
  char* cset;
  MirInfo(int ord)
    : CutInfo(MirCutKlass, ord)
    , n(0)
    , cset(NULL)
  {}

  ~MirInfo(){
    clearCSet();
  }
  void clearCSet(){
    if(cset != NULL){
      delete cset;
      n = 0;
      cset = NULL;
    }
  }
  void initCSet(int nvars){
    clearCSet();
    n = nvars;
    cset = new char[1+nvars];
  }
};

struct GmiInfo : public CutInfo {

  PrimitiveVec tab_row;
  int* tab_statuses;
  /* has the length tab_row.length */

  GmiInfo(int ord)
    : CutInfo(GmiCutKlass, ord)
    , tab_row()
    , tab_statuses(NULL)
  {
    Assert(!initialized_tab());
  }

  ~GmiInfo(){
    if(initialized_tab()){
      clear_tab();
    }
  }

  bool initialized_tab() const {
    return tab_statuses != NULL;
  }

  void init_tab(int N){
    if(initialized_tab()){
      clear_tab();
    }
    tab_row.setup(N);
    tab_statuses = new int[1+N];
  }

  void clear_tab() {
    delete[] tab_statuses;
    tab_statuses = NULL;
    tab_row.clear();
  }
};

static void loadCut(glp_tree *tree, CutInfo* cut){
  int ord, cut_len, cut_klass;
  int* cut_inds;
  double* cut_coeffs;
  int* cut_type;
  double* cut_rhs;

  ord = cut->ord;

  // Get the cut
  cut_len = glp_ios_get_cut(tree, ord, NULL, NULL, &cut_klass, NULL, NULL);
  cut->init_cut(cut_len);
  Assert(fromGlpkClass(cut_klass) == cut->klass);

  PrimitiveVec& cut_vec = cut->cut_vec;
  cut_inds = cut_vec.inds;
  cut_coeffs = cut_vec.coeffs;
  cut_type = &(cut->cut_type);
  cut_rhs = &(cut->cut_rhs);

  cut_vec.len = glp_ios_get_cut(tree, ord, cut_inds, cut_coeffs, &cut_klass, cut_type, cut_rhs);
  Assert(fromGlpkClass(cut_klass) == cut->klass);
  Assert(cut_vec.len == cut_len);
}

static MirInfo* mirCut(glp_tree *tree, int cut_ord){
  cout << "mirCut()" << endl;

  MirInfo* mir;
  int nrows;

  mir = new MirInfo(cut_ord);
  loadCut(tree, mir);

  nrows = glp_ios_cut_get_aux_nrows(tree, cut_ord);

  PrimitiveVec& row_sum = mir->row_sum;
  row_sum.setup(nrows);
  glp_ios_cut_get_aux_rows(tree, cut_ord, row_sum.inds, row_sum.coeffs);

  static int mir_id = 0;
  mir_id++;
  cout << "mir_id: " << mir_id << endl;
  row_sum.print(cout);

  return mir;
}

static GmiInfo* gmiCut(glp_tree *tree, int cut_ord){
  cout << "gmiCut()" << endl;

  int N;
  int M;
  int gmi_var;
  int write_pos;
  int read_pos;
  int stat;
  int ind;
  int i;

  GmiInfo* gmi;
  glp_prob* lp;

  gmi = new GmiInfo(cut_ord);
  loadCut(tree, gmi);

  lp = glp_ios_get_prob(tree);

  N = glp_get_num_cols(lp);
  M = glp_get_num_rows(lp);


  // Get the tableau row
  int nrows CVC4_UNUSED = glp_ios_cut_get_aux_nrows(tree, gmi->ord);
  Assert(nrows == 1);
  int rows[1+1];
  glp_ios_cut_get_aux_rows(tree, gmi->ord, rows, NULL);
  gmi_var = rows[1];

  gmi->init_tab(N);
  PrimitiveVec& tab_row = gmi->tab_row;
  cout << "Is N sufficient here?" << endl;
  tab_row.len = glp_eval_tab_row(lp, M+gmi_var, tab_row.inds, tab_row.coeffs);

  cout << "gmi_var " << gmi_var << endl;

  cout << "tab_pos " << tab_row.len << endl;
  write_pos = 1;
  for(read_pos = 1; read_pos <= tab_row.len; ++read_pos){
    if (fabs(tab_row.coeffs[read_pos]) < 1e-10){
    }else{
      tab_row.coeffs[write_pos] = tab_row.coeffs[read_pos];
      tab_row.inds[write_pos] = tab_row.inds[read_pos];
      ++write_pos;
    }
  }
  tab_row.len = write_pos-1;
  cout << "write_pos " << write_pos << endl;
  Assert(tab_row.len > 0);

  for(i = 1; i <= tab_row.len; ++i){
    ind = tab_row.inds[i];
    cout << "ind " << i << " " << ind << endl;
    stat = (ind <= M) ? glp_get_row_stat(lp, ind) : glp_get_col_stat(lp, ind-M);

    switch (stat){
    case GLP_NL:
    case GLP_NU:
    case GLP_NS:
      gmi->tab_statuses[i] = stat;
      break;
    case GLP_NF:
    default:
      Unreachable();
    }
  }
  gmi->print(cout);
  return gmi;
}

static void stopAtBingoOrPivotLimit(glp_tree *tree, void *info){
  AuxInfo* aux = (AuxInfo*)(info);
  int pivotLimit = aux->pivotLimit;
  TreeLog& tl = aux->tl;

  switch(glp_ios_reason(tree)){
  case GLP_IBINGO:
    glp_ios_terminate(tree);
    break;
  case GLP_ICUTADDED:
    {
      int cut_ord = glp_ios_pool_size(tree);
      int glpk_node = glp_ios_curr_node(tree);
      Assert(cut_ord > 0);
      cout << "tree size " << cut_ord << endl;
      cout << "curr node " << glpk_node << endl;
      int klass;
      glp_ios_get_cut(tree, cut_ord, NULL, NULL, &klass, NULL, NULL);

      switch(klass){
      case GLP_RF_GMI:
        {
          GmiInfo* gmi = gmiCut(tree, cut_ord);
          tl.addCut(glpk_node, gmi);
        }
        break;
      case GLP_RF_MIR:
        {
          MirInfo* mir = mirCut(tree, cut_ord);
          tl.addCut(glpk_node, mir);
        }
        break;
      case GLP_RF_COV:
        cout << "GLP_RF_COV" << endl;
        break;
      case GLP_RF_CLQ:
        cout << "GLP_RF_CLQ" << endl;
        break;
      default:
        break;
      }
    }
    break;
  default:
    {
      glp_prob* prob = glp_ios_get_prob(tree);
      int iterationcount = glp_get_it_cnt(prob);
      if(iterationcount > pivotLimit){
        glp_ios_terminate(tree);
      }
    }
    break;
  }
}

ApproximateSimplex::ApproxResult ApproxGLPK::solveMIP(){
  Assert(d_solvedRelaxation);
  // Explicitly disable presolving
  // We need the basis thus the presolver must be off!
  // This is default, but this is just being cautious.
  AuxInfo aux;
  aux.pivotLimit = d_pivotLimit;

  glp_iocp parm;
  glp_init_iocp(&parm);
  parm.presolve = GLP_OFF;
  parm.pp_tech = GLP_PP_NONE;
  parm.fp_heur = GLP_ON;
  parm.gmi_cuts = GLP_ON;
  parm.mir_cuts = GLP_ON;
  parm.cov_cuts = GLP_ON;
  parm.cb_func = stopAtBingoOrPivotLimit;
  parm.cb_info = &aux;
  parm.msg_lev = GLP_MSG_OFF;
  if(s_verbosity >= 1){
    parm.msg_lev = GLP_MSG_ALL;
  }
  int res = glp_intopt(d_prob, &parm);

  switch(res){
  case 0:
  case GLP_ESTOP:
    {
      int status = glp_mip_status(d_prob);
      switch(status){
      case GLP_OPT:
      case GLP_FEAS:
        d_solvedMIP = true;
        return ApproxSat;
      case GLP_NOFEAS:
        d_solvedMIP = true;
        return ApproxUnsat;
      default:
        return ApproxError;
      }
    }
  default:
    return ApproxError;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
#endif /*#ifdef CVC4_USE_GLPK */
/* End GPLK implementation. */
