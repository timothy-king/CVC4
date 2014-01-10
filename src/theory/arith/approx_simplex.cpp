#include "cvc4autoconfig.h"

#include "theory/arith/approx_simplex.h"
#include "theory/arith/normal_form.h"
#include "theory/arith/constraint.h"
#include <math.h>
#include <cmath>
#include <map>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

struct CutScratchPad {
  ArithVar d_basic; // a variable that is basic in the approximate solver
  DenseMap<Rational> d_tabRow;    // a row in the tableau not including d_basic
  DenseMap<Constraint> d_toBound; // each variable in toBound maps each variable in tabRow to either an upper/lower bound


  bool d_failure; // if the construction was unsuccessful
  DenseMap<Rational> d_cutLhs; //
  Rational d_cutRhs;
  std::set<Constraint> d_explanation; // use pointer equality
  CutScratchPad(){
    clear();
  }
  void clear(){
    d_basic = ARITHVAR_SENTINEL;
    d_tabRow.purge();
    d_toBound.purge(); // each variable in toBound maps each variable in tabRow to either an upper/lower bound

    d_failure = false;
    d_cutLhs.purge();
    d_cutRhs = Rational(0);
    d_explanation.clear();
  }
};

struct AuxInfo {
  TreeLog* tl;
  int pivotLimit;
  int branchLimit;
};

PrimitiveVec::PrimitiveVec()
  : len(0)
  , inds(NULL)
  , coeffs(NULL)
{}

PrimitiveVec::~PrimitiveVec(){
  clear();
}
bool PrimitiveVec::initialized() const {
  return inds != NULL;
}
void PrimitiveVec::clear() {
  if(initialized()){
    delete[] inds;
    delete[] coeffs;
    len = 0;
    inds = NULL;
    coeffs = NULL;
  }
}
void PrimitiveVec::setup(int l){
  Assert(!initialized());
  len = l;
  inds = new int[1+len];
  coeffs = new double[1+len];
}
void PrimitiveVec::print(std::ostream& out) const{
  Assert(initialized());
  out << len << " ";
  for(int i = 1; i <= len; ++i){
    out << "["<< inds[i] <<", " << coeffs[i]<<"]";
  }
  out << endl;
}

CutInfo::CutInfo(CutInfoKlass kl, int eid, int o)
  : execOrd(eid)
  , klass(kl)
  , ord(o)
  , cut_type_(kind::UNDEFINED_KIND)
  , cut_rhs()
  , cut_vec()
  , M(-1)
  , row_id(-1)
  , asLiteral(Node::null())
  , explanation(Node::null())
{}

void CutInfo::print(ostream& out) const{
  out << ord << " " << cut_type_ << " " << cut_rhs << endl;
  cut_vec.print(out);
}

void CutInfo::init_cut(int l){
  cut_vec.setup(l);
}

NodeLog::NodeLog()
  : d_nid(-1)
  , d_cuts()
  , d_rowIdsSelected()
  , stat(Open)
  , br_var(-1)
  , br_val(0.0)
  , dn(-1)
  , up(-1)
{}

NodeLog::NodeLog(int node)
  : d_nid(node)
  , d_cuts()
  , d_rowIdsSelected()
  , stat(Open)
  , br_var(-1)
  , br_val(0.0)
  , dn(-1)
  , up(-1)
{}

NodeLog::~NodeLog(){
  CutSet::iterator i = d_cuts.begin(), iend = d_cuts.end();
  for(; i != iend; ++i){
    CutInfo* c = *i;
    delete c;
  }
  d_cuts.clear();
  Assert(d_cuts.empty());
}

int NodeLog::getNodeId() const {
  return d_nid;
}
void NodeLog::addSelected(int ord, int sel){
  d_rowIdsSelected[ord] = sel;
  cout << "addSelected("<< ord << ", "<< sel << ")" << endl;
}
void NodeLog::applySelected() {
  CutSet::iterator iter = d_cuts.begin(), iend = d_cuts.end(), todelete;
  while(iter != iend){
    CutInfo* curr = *iter;
    if(curr->klass == BranchCutKlass){
      // skip
      ++iter;
    }else if(d_rowIdsSelected.find(curr->ord) == d_rowIdsSelected.end()){
      todelete = iter;
      ++iter;
      d_cuts.erase(todelete);
      delete curr;
    }else{
      curr->row_id = d_rowIdsSelected[curr->ord];
      ++iter;
    }
  }
}


void NodeLog::addCut(CutInfo* ci){
  Assert(ci != NULL);
  d_cuts.insert(ci);
}

// void NodeLog::shrinkCuts(size_t n){
//   Assert(n <= d_cuts.size());
//   while(d_cuts.size() > n){
//     CutInfo* cut = d_cuts.back();
//     d_cuts.pop_back();
//     delete cut;
//   }
//   Assert(d_cuts.size() == n);
// }

void NodeLog::print(ostream& o) const{
  o << "[n" << getNodeId();
  for(const_iterator iter = begin(), iend = end(); iter != iend; ++iter ){
    CutInfo* cut = *iter;
    o << ", " << cut->ord;
    if(cut->row_id >= 0){
      o << " " << cut->row_id;
    }
  }
  o << "]" << std::endl;
}

void NodeLog::closeNode(){
  Assert(stat == Open);
  stat = Closed;
}

void NodeLog::setBranchVal(int br, double val){
  Assert(stat == Open);
  br_var = br; br_val = val;
}
void NodeLog::setChildren(int d, int u){
  Assert(stat == Open);
  dn = d; up = u;
  stat = Branched;
}

TreeLog::TreeLog()
  : d_toNode()
{
  // add root
  int rid = 1;
  d_toNode.insert(make_pair(rid, NodeLog(rid)));
}

void TreeLog::branch(int nid, int br, double val, int dn, int up){
  NodeLog& nl = getNode(nid);
  nl.setBranchVal(br, val);
  nl.setChildren(dn, up);

  d_toNode.insert(make_pair(dn, NodeLog(dn)));
  d_toNode.insert(make_pair(up, NodeLog(up)));
}

void TreeLog::close(int nid){
  NodeLog& nl = getNode(nid);
  nl.closeNode();
}

void TreeLog::branchClose(int nid, int br, double val){
  NodeLog& nl = getNode(nid);
  nl.setBranchVal(br, val);
  nl.closeNode();
}

// void TreeLog::addCut(int nid, CutInfo* ci){
//   if(d_toNode.find(nid) == d_toNode.end()){
//     d_toNode.insert(make_pair(nid, NodeLog(nid) ));
//   }
//   NodeLog& node = d_toNode[nid];
//   node.addCut(ci);
// }

// void TreeLog::addSelected(int nid, int ord, int sel){
//   Assert(d_toNode.find(nid) != d_toNode.end());

//   NodeLog& node = d_toNode[nid];
//   node.addSelected(ord, sel);
// }

void TreeLog::applySelected() {
  std::map<int, NodeLog>::iterator iter, end;
  for(iter = d_toNode.begin(), end = d_toNode.end(); iter != end; ++iter){
    NodeLog& onNode = (*iter).second;
    onNode.applySelected();
  }
}

void TreeLog::print(ostream& o) const{
  o << "TreeLog: " << d_toNode.size() << std::endl;
  for(const_iterator iter = begin(), iend = end(); iter != iend; ++iter){
    const NodeLog& onNode = (*iter).second;
    onNode.print(o);
  }
}


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
      cout << "  cfe["<<i<<"]: " << back << endl;
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

// Rational ApproximateSimplex::estimateWithCFE(const Rational& q, int depth){
//   cout << "estimateWithCFE("<<q<<", "<<depth<<")"<<endl;
//   std::vector<Integer> cfe = rationalToCfe(q,depth);
//   return cfeToRational(cfe);
// }


Rational ApproximateSimplex::estimateWithCFE(const Rational& r, const Integer& K){
  cout << "estimateWithCFE(" << r << ", " << K << ")" <<endl;
  // references
  // page 4: http://carlossicoli.free.fr/C/Cassels_J.W.S.-An_introduction_to_diophantine_approximation-University_Press(1965).pdf
  // http://en.wikipedia.org/wiki/Continued_fraction
  Assert(K >= Integer(1));
  if( r.getDenominator() <= K ){
    return r;
  }else if( K.isOne() ){
    return Rational(r.floor());
  }

  // current numerator and denominator that has not been resolved in the cfe
  Integer num = r.getNumerator(), den = r.getDenominator();
  Integer quot,rem;

  unsigned t = 0;
  // For a sequence of candidate solutions q_t/p_t
  // we keep only 3 time steps: 0[prev], 1[current], 2[next]
  // timesteps with a fake timestep 0 (p is 0 and q is 1)
  // at timestep 1
  Integer p[3]; // h
  Integer q[3]; // k
  // load the first 3 time steps manually
  p[0] =    0; q[0] = 1; // timestep -2
  p[1] =    1; q[1] = 0; // timestep -1

  Integer::floorQR(quot, rem, num, den);
  num = den; den = rem;

  q[2] = q[0] + quot*q[1];
  p[2] = p[0] + quot*p[1];

  cout << "  cfe["<<t<<"]: " << p[2] <<"/"<< q[2] << endl;
  while( q[2] <= K ){
    p[0] = p[1]; p[1] = p[2];
    q[0] = q[1]; q[1] = q[2];


    Integer::floorQR(quot, rem, num, den);
    num = den; den = rem;

    p[2] = p[0]+quot*p[1];
    q[2] = q[0]+quot*q[1];
    ++t;
    cout << "  cfe["<<t<<"]: " << p[2] <<"/"<< q[2] << endl;
  }

  Integer k = (K-q[0]).floorDivideQuotient(q[1]);
  Rational cand_prev(p[0]+k*p[1], q[0]+k*q[1]);
  Rational cand_curr(p[1], q[1]);
  Rational dist_prev = (cand_prev - r).abs();
  Rational dist_curr = (cand_curr - r).abs();
  if(dist_prev <= dist_curr){
    cout<< cand_prev << " is closer than " << cand_curr << endl;
    return cand_prev;
  }else{
    cout<< cand_curr << " is closer than " << cand_prev << endl;
    return cand_curr;
  }
}

Rational ApproximateSimplex::estimateWithCFE(double d){
  Integer maxInt(1<<26);
  return estimateWithCFE(Rational::fromDouble(d), maxInt);
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

Kind glpk_type_to_kind(int glpk_cut_type){
  switch(glpk_cut_type){
  case GLP_LO: return kind::LEQ;
  case GLP_UP: return kind::GEQ;
  case GLP_FX: return kind::EQUAL;
  case GLP_DB:
  case GLP_FR:
  default:     return kind::UNDEFINED_KIND;
  }
}

class GmiInfo;
class MirInfo;
class BranchCutInfo;

class ApproxGLPK : public ApproximateSimplex {
private:
  glp_prob* d_prob;
  const ArithVariables& d_vars;

  DenseMap<int> d_colIndices;
  DenseMap<int> d_rowIndices;

  DenseMap<ArithVar> d_rowToArithVar;
  DenseMap<ArithVar> d_colToArithVar;

  int d_instanceID;

  bool d_solvedRelaxation;
  bool d_solvedMIP;

  static int s_verbosity;

  CutScratchPad d_pad;

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

  // get this stuff out of here
  void tryCut(int nid, CutInfo& cut);

  ArithVar _getArithVar(int nid, int M, int ind) const;
  bool guessIsConstructable(const DenseMap<Rational>& guess) const;
  bool loadToBound(int node, int M, int len, int* inds, int* statuses, DenseMap<Constraint>& toBound) const;
  bool checkCutOnPad(int nid, CutInfo& cut) const;
  void finalizeCut(int nid, CutInfo& cut) const;
  void attemptGmi(int nid, GmiInfo& gmi);
  void attemptConstructTableRow(int node, int M, const PrimitiveVec& vec);

  void constructGmiCut();
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
      d_rowToArithVar.set(numRows, v);
      cout << "Row vars: " << v << "<->" << numRows << endl;
    }else{
      ++numCols;
      d_colIndices.set(v, numCols);
      d_colToArithVar.set(numCols, v);
      cout << "Col vars: " << v << "<->" << numCols << endl;
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
  MirInfo(int execOrd, int ord)
    : CutInfo(MirCutKlass, execOrd, ord)
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
  int basic;
  PrimitiveVec tab_row;
  int* tab_statuses;
  /* has the length tab_row.length */

  GmiInfo(int execOrd, int ord)
    : CutInfo(GmiCutKlass, execOrd, ord)
    , basic(-1)
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
    basic = -1;
  }
};

struct BranchCutInfo : public CutInfo {
  BranchCutInfo(int execOrd, int br,  Kind dir, double val)
    : CutInfo(BranchCutKlass, execOrd, 0)
  {
    init_cut(1);
    cut_vec.inds[1] = br;
    cut_vec.coeffs[1] = +1.0;
    cut_rhs = val;
    cut_type_ = dir;
  }
};


static void loadCut(glp_tree *tree, CutInfo* cut){
  int ord, cut_len, cut_klass;
  int* cut_inds;
  double* cut_coeffs;
  int glpk_cut_type;
  double* cut_rhs;

  ord = cut->ord;

  // Get the cut
  cut_len = glp_ios_get_cut(tree, ord, NULL, NULL, &cut_klass, NULL, NULL);
  cut->init_cut(cut_len);
  Assert(fromGlpkClass(cut_klass) == cut->klass);

  PrimitiveVec& cut_vec = cut->cut_vec;
  cut_inds = cut_vec.inds;
  cut_coeffs = cut_vec.coeffs;
  cut_rhs = &(cut->cut_rhs);

  cut_vec.len = glp_ios_get_cut(tree, ord, cut_inds, cut_coeffs, &cut_klass, &glpk_cut_type, cut_rhs);
  Assert(fromGlpkClass(cut_klass) == cut->klass);
  Assert(cut_vec.len == cut_len);

  cut->cut_type_ = glpk_type_to_kind(glpk_cut_type);
  Assert(cut->cut_type_ == kind::LEQ || cut->cut_type_ == kind::GEQ);
}


static MirInfo* mirCut(glp_tree *tree, int exec_ord, int cut_ord){
  cout << "mirCut()" << endl;

  MirInfo* mir;
  int nrows;

  mir = new MirInfo(exec_ord, cut_ord);
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

static GmiInfo* gmiCut(glp_tree *tree, int exec_ord, int cut_ord){
  cout << "gmiCut()" << endl;

  int N;
  int gmi_var;
  int write_pos;
  int read_pos;
  int stat;
  int ind;
  int i;

  GmiInfo* gmi;
  glp_prob* lp;

  gmi = new GmiInfo(exec_ord, cut_ord);
  loadCut(tree, gmi);

  lp = glp_ios_get_prob(tree);

  N = glp_get_num_cols(lp);
  gmi->M = glp_get_num_rows(lp);


  // Get the tableau row
  int nrows CVC4_UNUSED = glp_ios_cut_get_aux_nrows(tree, gmi->ord);
  Assert(nrows == 1);
  int rows[1+1];
  glp_ios_cut_get_aux_rows(tree, gmi->ord, rows, NULL);
  gmi_var = rows[1];

  gmi->init_tab(N);
  gmi->basic = gmi->M+gmi_var;
  cout << gmi <<" " << gmi->basic << " "
       << cut_ord<<" "  << gmi->M <<" " << gmi_var << endl;

  PrimitiveVec& tab_row = gmi->tab_row;
  cout << "Is N sufficient here?" << endl;
  tab_row.len = glp_eval_tab_row(lp, gmi->basic, tab_row.inds, tab_row.coeffs);

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
    stat = (ind <= gmi->M) ?
      glp_get_row_stat(lp, ind) : glp_get_col_stat(lp, ind - gmi->M);

    cout << "ind " << i << " " << ind << " stat " << stat << endl;
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

static BranchCutInfo* branchCut(glp_tree *tree, int exec_ord, int br_var, double br_val, bool down_bad){
  //(tree, br_var, br_val, dn < 0);
  double rhs;
  Kind k;
  if(down_bad){
    // down branch is infeasible
    // new lower bound
    k = kind::GEQ;
    rhs = std::ceil(br_val);
  }else{
    // down branch is infeasible
    // new upper bound
    k = kind::LEQ;
    rhs = std::floor(br_val);
  }
  BranchCutInfo* br_cut = new BranchCutInfo(exec_ord, br_var, k, rhs);
  return br_cut;
}

static void stopAtBingoOrPivotLimit(glp_tree *tree, void *info){
  AuxInfo* aux = (AuxInfo*)(info);
  int pivotLimit = aux->pivotLimit;
  TreeLog& tl = *(aux->tl);

  int exec = tl.getExecutionOrd();
  int glpk_node_p = -1;
  int node_ord = -1;

  switch(glp_ios_reason(tree)){
  case GLP_IBINGO:
    glp_ios_terminate(tree);
    break;
  case GLP_ICUTADDED:
    {
      int cut_ord = glp_ios_pool_size(tree);
      glpk_node_p = glp_ios_curr_node(tree);
      node_ord = glp_ios_node_ord(tree, glpk_node_p);
      Assert(cut_ord > 0);
      cout << "tree size " << cut_ord << endl;
      cout << "curr node " << glpk_node_p << endl;
      cout << "depth " << glp_ios_node_level(tree, glpk_node_p) << endl;
      int klass;
      glp_ios_get_cut(tree, cut_ord, NULL, NULL, &klass, NULL, NULL);

      NodeLog& node = tl.getNode(node_ord);
      switch(klass){
      case GLP_RF_GMI:
        {
          GmiInfo* gmi = gmiCut(tree, exec, cut_ord);
          node.addCut(gmi);
        }
        break;
      case GLP_RF_MIR:
        {
          MirInfo* mir = mirCut(tree, exec, cut_ord);
          node.addCut(mir);
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
  case GLP_ICUTSELECT:
    {
      glpk_node_p = glp_ios_curr_node(tree);
      node_ord = glp_ios_node_ord(tree, glpk_node_p);
      int cuts = glp_ios_pool_size(tree);
      int* ords = new int[1+cuts];
      int* rows = new int[1+cuts];
      int N = glp_ios_selected_cuts(tree, ords, rows);

      NodeLog& nl = tl.getNode(node_ord);
      cout << glpk_node_p << " " << node_ord << " " << cuts << " " << N << std::endl;
      for(int i = 1; i <= N; ++i){
        nl.addSelected(ords[i], rows[i]);
      }
      delete[] ords;
      delete[] rows;
    }
    break;
  case GLP_LI_BRANCH:
    {
      // a branch was just made
      int br_var;
      int p, dn, up;
      int p_ord, dn_ord, up_ord;
      double br_val;
      br_var = glp_ios_branch_log(tree, &br_val, &p, &dn, &up);
      p_ord = glp_ios_node_ord(tree, p);
      if(dn >= 0){ dn_ord = glp_ios_node_ord(tree, dn); }
      if(up >= 0){ up_ord = glp_ios_node_ord(tree, up); }

      cout << "branch: "<< br_var << " "  << br_val << " tree " << p << " " << dn << " " << up << endl;
      cout << "\t " << p_ord << " " << dn_ord << " " << up_ord << endl;
      if(dn < 0 && up < 0){
        cout << "branch close" << endl;
        tl.branchClose(p_ord, br_var, br_val);
      }else if(dn < 0 || up < 0){
        cout << "branch cut" << endl;
        NodeLog& node = tl.getNode(p_ord);
        BranchCutInfo* cut_br = branchCut(tree, exec, br_var, br_val, dn < 0);
        node.addCut(cut_br);
      }else{
        cout << "normal branch" << endl;
        tl.branch(p_ord, br_var, br_val, dn_ord, up_ord);
      }
    }
    break;
  case GLP_LI_CLOSE:
    {
      glpk_node_p = glp_ios_curr_node(tree);
      node_ord = glp_ios_node_ord(tree, glpk_node_p);
      cout << "close " << glpk_node_p << endl;
      tl.close(node_ord);
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
  aux.branchLimit = d_branchLimit;
  aux.tl = &d_log;

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

  d_log.print(cout);
  d_log.applySelected();
  d_log.print(cout);

  for(TreeLog::const_iterator i = d_log.begin(), iend=d_log.end(); i!=iend;++i){
    int nid = (*i).first;
    const NodeLog& con = (*i).second;
    for(NodeLog::const_iterator j = con.begin(),jend=con.end(); j!=jend;++j){
      CutInfo* cut = *j;
      tryCut(nid, *cut);
    }
  }

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



Node explainSet(const set<Constraint>& inp){
  Assert(!inp.empty());
  NodeBuilder<> nb(kind::AND);
  set<Constraint>::const_iterator iter, end;
  for(iter = inp.begin(), end = inp.end(); iter != end; ++iter){
    const Constraint c = *iter;
    Assert(c != NullConstraint);
    c->explainForConflict(nb);
  }
  Node ret = safeConstructNary(nb);
  Node rew = Rewriter::rewrite(ret);
  if(rew.getNumChildren() < ret.getNumChildren()){
    cout << "explainSet " << ret << " " << rew << endl;
  }
  return rew;
}

DeltaRational sumConstraints(const DenseMap<Rational>& xs, const DenseMap<Constraint>& cs, bool* anyinf){
  if(anyinf != NULL){
    *anyinf = false;
  }

  DeltaRational beta(0);
  DenseMap<Rational>::const_iterator iter, end;
  iter = xs.begin();
  end = xs.end();
  cout << "sumConstraints";
  for(; iter != end; ++iter){
    ArithVar x = *iter;
    const Rational& psi = xs[x];
    Constraint c = cs[x];
    Assert(c != NullConstraint);

    const DeltaRational& bound = c->getValue();
    beta += bound * psi;
    cout << " +("<<bound << "*" << psi <<")";
    if(anyinf != NULL ){
      *anyinf = *anyinf || !bound.infinitesimalIsZero();
    }
  }
  cout << "= " << beta << endl;
  return beta;
}

// remove fixed variables from the vector
Rational removeFixed(const ArithVariables& vars, DenseMap<Rational>& vec, set<Constraint>& exp){
  Rational removed(0);
  vector<ArithVar> equal;
  DenseMap<Rational>::const_iterator vec_iter, vec_end;
  vec_iter = vec.begin(), vec_end = vec.end();
  for(; vec_iter != vec_end; ++vec_iter){
    ArithVar x = *vec_iter;
    if(vars.boundsAreEqual(x)){
      equal.push_back(x);
    }
  }
  vector<ArithVar>::const_iterator equal_iter, equal_end;
  equal_iter = equal.begin(), equal_end = equal.end();
  for(; equal_iter != equal_end; ++equal_iter){
    ArithVar x = *equal_iter;
    Assert(vars.boundsAreEqual(x));
    const DeltaRational& lb = vars.getLowerBound(x);
    Assert(lb.infinitesimalIsZero());
    removed += (vec[x]) * lb.getNoninfinitesimalPart();

    vec.remove(x);

    std::pair<Constraint, Constraint> p = vars.explainEqualBounds(x);
    exp.insert(p.first);
    cout << p.first << endl;
    if(p.second != NullConstraint){
      exp.insert(p.second);
      cout << p.second << endl;
    }
  }
  return removed;
}
void removeZeroes(DenseMap<Rational>& v){
  // Remove Slack variables
  vector<ArithVar> zeroes;
  DenseMap<Rational>::const_iterator i, iend;
  for(i = v.begin(), iend = v.end(); i != iend; ++i){
    ArithVar x = *i;
    if(v[x].isZero()){
      zeroes.push_back(x);
    }
  }

  vector<ArithVar>::const_iterator j, jend;
  for(j = zeroes.begin(), jend = zeroes.end(); j != jend; ++j){
    ArithVar x = *j;
    v.remove(x);
  }
}
void removeSlackVariables(const ArithVariables& vars, DenseMap<Rational>& vec){
  // Remove Slack variables
  vector<ArithVar> slacks;
  DenseMap<Rational>::const_iterator vec_iter, vec_end;
  vec_iter = vec.begin(), vec_end = vec.end();
  for(; vec_iter != vec_end; ++vec_iter){
    ArithVar x = *vec_iter;
    if(vars.isSlack(x)){
      slacks.push_back(x);
    }
  }

  vector<ArithVar>::const_iterator slack_iter, slack_end;
  slack_iter = slacks.begin(), slack_end = slacks.end();
  for(; slack_iter != slack_end; ++slack_iter){
    ArithVar s = *slack_iter;
    const Rational& s_coeff = vec[s];
    Assert(vars.isSlack(s));
    Assert(vars.hasNode(s));
    Node sAsNode = vars.asNode(s);
    Polynomial p = Polynomial::parsePolynomial(sAsNode);
    for(Polynomial::iterator j = p.begin(), p_end=p.end(); j != p_end; ++j){
      Monomial m = *j;
      const Rational& ns_coeff = m.getConstant().getValue();
      Node vl = m.getVarList().getNode();
      ArithVar ns = vars.asArithVar(vl);
      Rational prod = s_coeff * ns_coeff;
      if(vec.isKey(ns)){
        vec.get(ns) += prod;
      }else{
        vec.set(ns, prod);
      }
    }
    // remove s
    vec.remove(s);
  }
  removeZeroes(vec);
}

ArithVar ApproxGLPK::_getArithVar(int nid, int M, int ind) const{
  Assert(ind >= 0);
  if(ind <= M){
    // this is a row
    if((unsigned)ind < d_rowToArithVar.size()){
      return d_rowToArithVar[ind];
    }else{
      // replace by a looking up this new row
      Assert(false);
      return ARITHVAR_SENTINEL;
    }
  }else{
    int col_ord = ind - M;
    Assert(col_ord >= 0);
    return d_colToArithVar[(unsigned)col_ord];
  }
}

void printDV(ostream& out, const DenseMap<Rational>& v){
  out << "[DenseVec len " <<  v.size();
  DenseMap<Rational>::const_iterator iter, end;
  for(iter = v.begin(), end = v.end(); iter != end; ++iter){
    ArithVar x = *iter;
    out << ", "<< x << " " << v[x];
  }
  out << "]";
}

bool ApproxGLPK::guessIsConstructable(const DenseMap<Rational>& guess) const {
  // basic variable
  // sum g[i] * x_i
  DenseMap<Rational> g = guess;
  removeSlackVariables(d_vars, g);
  cout << "guessIsConstructable " << g.size() << endl;
  printDV(cout, g);
  return g.empty();
}

bool ApproxGLPK::loadToBound(int nid, int M, int len, int* inds, int* statuses, DenseMap<Constraint>& toBound) const{
  for(int i = 1; i <= len; ++i){
    int status = statuses[i];
    int ind = inds[i];
    ArithVar v = _getArithVar(nid, M, ind);
    Constraint c = NullConstraint;
    if(v == ARITHVAR_SENTINEL){ return true; }

    switch(status){
    case GLP_NL:
      c = d_vars.getLowerBoundConstraint(v);
      break;
    case GLP_NU:
    case GLP_NS: // upper bound sufficies for fixed variables
      c = d_vars.getUpperBoundConstraint(v);
      break;
    case GLP_NF:
    default:
      return true;
    }
    if(c == NullConstraint){
      cout << "couldn't find " << v << " @ " << nid << endl;
      return true;
    }
    Assert(c != NullConstraint);
    toBound.set(v, c);
  }
  return false;
}

bool ApproxGLPK::checkCutOnPad(int nid, CutInfo& cut) const{

  const DenseMap<Rational>& constructedLhs = d_pad.d_cutLhs;
  const Rational& constructedRhs = d_pad.d_cutRhs;
  hash_set<ArithVar> visited;

  if(constructedLhs.empty()){ return true; }

  double norm = (cut.cut_type_ == kind::LEQ ? + 1.0 : - 1.0);

  double normRhs = norm * cut.cut_rhs;
  if(!roughlyEqual(normRhs, constructedRhs.getDouble())){ cout << "failure"; return true; }
  const PrimitiveVec& cv = cut.cut_vec;
  for(int i = 1; i <= cv.len; ++i){
    int ind = cv.inds[i]; // this is always a structural variable
    double coeff = cv.coeffs[i];
    double norm_coeff = norm * coeff;

    if(!d_colToArithVar.isKey(ind)){ return true; }
    ArithVar x = d_colToArithVar[ind];
    //if(x == ARITHVAR_SENTINEL){ return true; }
    visited.insert(x);

    if(!constructedLhs.isKey(x)){ return true; }
    const Rational& onConstructed = constructedLhs[x];
    if(!roughlyEqual(norm_coeff, onConstructed.getDouble())){
      cout << "failure"; return true;
    }
  }
  if(visited.size() != constructedLhs.size()){ return true; }
  return false;
}

Node toSumNode(const ArithVariables& vars, const DenseMap<Rational>& sum){
  NodeBuilder<> nb(kind::PLUS);
  NodeManager* nm = NodeManager::currentNM();
  DenseMap<Rational>::const_iterator iter, end;
  iter = sum.begin(), end = sum.end();
  for(; iter != end; ++iter){
    ArithVar x = *iter;
    if(!vars.hasNode(x)){ return Node::null(); }
    Node xNode = vars.asNode(x);
    const Rational& q = sum[x];
    nb << nm->mkNode(kind::MULT, mkRationalNode(q), xNode);
  }
  return safeConstructNary(nb);
}

void ApproxGLPK::finalizeCut(int nid, CutInfo& cut) const{
  Assert(!d_pad.d_failure);
  Assert(!d_pad.d_cutLhs.empty());

  NodeManager* nm = NodeManager::currentNM();
  Node sumLhs = toSumNode(d_vars, d_pad.d_cutLhs);
  Node ineq = nm->mkNode(kind::GEQ, sumLhs, mkRationalNode(d_pad.d_cutRhs) );

  cut.asLiteral = Rewriter::rewrite(ineq);
  cut.explanation = explainSet(d_pad.d_explanation);

  cout << "commit the cut: " <<cut.asLiteral <<  cut.explanation << endl;
}

void ApproxGLPK::attemptGmi(int nid, GmiInfo& gmi){
  d_pad.clear();

  ArithVar b = _getArithVar(nid, gmi.M, gmi.basic);
  if(b == ARITHVAR_SENTINEL){
    d_pad.d_failure = true; return;
  }
  if(!d_vars.isInteger(b)){
    d_pad.d_failure = true; return;
  }
  d_pad.d_basic = b;


  PrimitiveVec& tab = gmi.tab_row;
  attemptConstructTableRow(nid, gmi.M, tab);
  if(d_pad.d_failure){ return; }

  d_pad.d_failure = loadToBound(nid, gmi.M, tab.len, tab.inds, gmi.tab_statuses, d_pad.d_toBound);
  if(d_pad.d_failure){ return; }

  constructGmiCut();
  if(d_pad.d_failure){ return; }

  d_pad.d_failure = checkCutOnPad(nid, gmi);
  if(d_pad.d_failure){ return; }

  finalizeCut(nid, gmi);
}

void ApproxGLPK::attemptConstructTableRow(int nid, int M, const PrimitiveVec& vec){
  ArithVar basic = d_pad.d_basic;
  DenseMap<Rational>& tab = d_pad.d_tabRow;
  Assert(basic != ARITHVAR_SENTINEL);

  cout << "attemptConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
  vec.print(cout);
  cout << "match " << basic << "("<<d_vars.asNode(basic)<<")"<<endl;

  tab.set(basic, Rational(-1));
  for(int i = 1; i <= vec.len; ++i){
    int ind = vec.inds[i];
    double coeff = vec.coeffs[i];
    ArithVar var = _getArithVar(nid, M, ind);
    if(var == ARITHVAR_SENTINEL){
      cout << "couldn't find" << var << endl;
      d_pad.d_failure = true; return;
    }
    cout << "match " << ind << "," << var << "("<<d_vars.asNode(var)<<")"<<endl;

    Rational cfe = estimateWithCFE(coeff);
    tab.set(var, cfe);
    cout << var << " cfe " << cfe << endl;
  }
  if(!guessIsConstructable(tab)){
    d_pad.d_failure = true; return;
  }
  tab.remove(basic);
}

/* Maps an ArithVar to either an upper/lower bound */
void ApproxGLPK::constructGmiCut(){
  const DenseMap<Rational>& tabRow = d_pad.d_tabRow;
  const DenseMap<Constraint>& toBound = d_pad.d_toBound;
  DenseMap<Rational>& cut = d_pad.d_cutLhs;
  std::set<Constraint>& explanation = d_pad.d_explanation;
  Rational& rhs = d_pad.d_cutRhs;

  DenseMap<Rational>::const_iterator iter, end;
  Assert(cut.empty());

  // compute beta for a "fake" assignment
  bool anyInf;
  DeltaRational dbeta = sumConstraints(tabRow, toBound, &anyInf);
  const Rational& beta = dbeta.getNoninfinitesimalPart();
  cout << dbeta << endl;
  if(anyInf || beta.isIntegral()){
    d_pad.d_failure = true; return; // this is going to fail
  }

  Rational one = Rational(1);
  Rational fbeta = beta.floor_frac();
  rhs = fbeta;
  Assert(fbeta.sgn() > 0);
  Assert(fbeta < one);
  Rational one_sub_fbeta = one - fbeta;
  for(iter = tabRow.begin(), end = tabRow.end(); iter != end; ++iter){
    ArithVar x = *iter;
    const Rational& psi = tabRow[x];
    Constraint c = toBound[x];
    const Rational& bound = c->getValue().getNoninfinitesimalPart();
    if(d_vars.boundsAreEqual(x)){
      // do not add a coefficient
      // implictly substitute the variable w/ its constraint
      std::pair<Constraint, Constraint> exp = d_vars.explainEqualBounds(x);
      explanation.insert(exp.first);
      cout << exp.first << endl;
      if(exp.second != NullConstraint){
        explanation.insert(exp.second);
        cout << exp.second << endl;
      }
    }else if(d_vars.isInteger(x) && psi.isIntegral()){
      // do not add a coefficient
      // nothing to explain
    }else{
      explanation.insert(c);
      Rational phi;
      Rational alpha = (c->isUpperBound() ? psi : -psi);

      // x - ub <= 0 and lb - x <= 0
      if(d_vars.isInteger(x)){
        Assert(!psi.isIntegral());
        // alpha = slack_sgn * psi
        Rational falpha = alpha.floor_frac();
        Assert(falpha.sgn() > 0);
        Assert(falpha < one);
        phi = (falpha <= fbeta) ?
          falpha : ((fbeta / one_sub_fbeta) * (one - falpha));
      }else{
        phi = (alpha >= 0) ?
          alpha : ((fbeta / one_sub_fbeta) * (- alpha));
      }
      Assert(phi.sgn() != 0);
      if(c->isUpperBound()){
        cut.set(x, -phi);
        rhs -= phi * bound;
      }else{
        cut.set(x, phi);
        rhs += phi * bound;
      }
    }
  }
  cout << "pre removeSlackVariables";
  printDV(cout, cut);
  removeSlackVariables(d_vars, cut);
  cout << "post removeSlackVariables";  printDV(cout, cut);
  Rational sumRemoved = removeFixed(d_vars, cut, explanation);
  cout << "post removeFixed";
  printDV(cout, cut);
  rhs -= sumRemoved;
  cout << "rhs " << rhs << " " <<sumRemoved << endl;
}

void ApproxGLPK::tryCut(int nid, CutInfo& cut){
  static int success = 0;
  static int attempts = 0;
  switch(cut.klass){
  case GmiCutKlass:
    attempts++;
    attemptGmi(nid, static_cast<GmiInfo&>(cut));
    if(!cut.asLiteral.isNull()){
      success++;
    }
    cout << "success rate :" << success << "/"<<attempts<<endl;
    break;
  case MirCutKlass:
    Unimplemented();
  default:
    break;
  }
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
#endif /*#ifdef CVC4_USE_GLPK */
/* End GPLK implementation. */
