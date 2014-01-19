#include "cvc4autoconfig.h"


#include "theory/arith/cut_log.h"
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

NodeLog::const_iterator NodeLog::begin() const { return d_cuts.begin(); }
NodeLog::const_iterator NodeLog::end() const { return d_cuts.end(); }

NodeLog& TreeLog::getNode(int nid) {
  ToNodeMap::iterator i = d_toNode.find(nid);
  Assert(i != d_toNode.end());
  return (*i).second;
}

TreeLog::const_iterator TreeLog::begin() const { return d_toNode.begin(); }
TreeLog::const_iterator TreeLog::end() const { return d_toNode.end(); }

int TreeLog::getExecutionOrd(){
  int res = next_exec_ord;
  ++next_exec_ord;
  return res;
}
void TreeLog::makeInactive(){  d_active = false; }
void TreeLog::makeActive(){  d_active = true; }
bool TreeLog::isActivelyLogging() const { return d_active; }


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
  out.precision(15);
  for(int i = 1; i <= len; ++i){
    out << "["<< inds[i] <<", " << coeffs[i]<<"]";
  }
  out << endl;
}

CutInfo::CutInfo(CutInfoKlass kl, int eid, int o)
  : d_klass(kl)
  , d_execOrd(eid)
  , d_poolOrd(o)
  , d_cutType(kind::UNDEFINED_KIND)
  , d_cutRhs()
  , d_cutVec()
  , d_mAtCreation(-1)
  , d_rowId(-1)
  , d_exactPrecision(NULL)
  , d_explanation(NULL)
{}

CutInfo::~CutInfo(){
  if(d_exactPrecision == NULL){ delete d_exactPrecision; }
  if(d_explanation == NULL){ delete d_explanation; }
}

int CutInfo::getId() const {
  return d_execOrd;
}

int CutInfo::getRowId() const{
  return d_rowId;
}

void CutInfo::setRowId(int rid){
  d_rowId = rid;
}

void CutInfo::print(ostream& out) const{
  out << "[CutInfo " << d_execOrd << " " << d_poolOrd
      << " " << d_klass << " " << d_cutType << " " << d_cutRhs;
  d_cutVec.print(out);
  out << "]" << endl;
}

PrimitiveVec& CutInfo::getCutVector(){
  return d_cutVec;
}

const PrimitiveVec& CutInfo::getCutVector() const{
  return d_cutVec;
}

// void CutInfo::init_cut(int l){
//   cut_vec.setup(l);
// }

Kind CutInfo::getKind() const{
  return d_cutType;
}

void CutInfo::setKind(Kind k){
  Assert(k == kind::LEQ || k == kind::GEQ);
  d_cutType = k;
}

double CutInfo::getRhs() const{
  return d_cutRhs;
}

void CutInfo::setRhs(double r){
  d_cutRhs = r;
}

bool CutInfo::success() const{
  return d_exactPrecision != NULL;
}

CutInfoKlass CutInfo::getKlass() const{
  return d_klass;
}

int CutInfo::poolOrdinal() const{
  return d_poolOrd;
}

void CutInfo::setDimensions(int N, int M){
  d_mAtCreation = M;
  d_N = N;
}

int CutInfo::getN() const{
  return d_N;
}

int CutInfo::getMAtCreation() const{
  return d_mAtCreation;
}

/* Returns true if the cut has an explanation. */
bool CutInfo::proven() const{
  return d_explanation != NULL;
}

bool CutInfo::operator<(const CutInfo& o) const{
  return d_execOrd < o.d_execOrd;
}


void CutInfo::setCut(const DenseVector& ep){
  Assert(!success());
  d_exactPrecision = new DenseVector(ep);
}

void CutInfo::setExplanation(const ConstraintCPVec& ex){
  Assert(success());
  Assert(!proven());
  if(d_explanation == NULL){
    d_explanation = new ConstraintCPVec(ex);
  }else{
    *d_explanation = ex;
  }
}

void CutInfo::swapExplanation(ConstraintCPVec& ex){
  Assert(success());
  Assert(!proven());
  if(d_explanation == NULL){
    d_explanation = new ConstraintCPVec();
  }
  d_explanation->swap(ex);
}

const DenseVector& CutInfo::getExactPrecision() const {
  Assert(success());
  return *d_exactPrecision;
}
const ConstraintCPVec& CutInfo::getExplanation() const {
  Assert(proven());
  return *d_explanation;
}

std::ostream& operator<<(std::ostream& os, const CutInfo& ci){
  ci.print(os);
  return os;
}

std::ostream& operator<<(std::ostream& out, CutInfoKlass kl){
  switch(kl){
  case MirCutKlass:
    out << "MirCutKlass"; break;
  case GmiCutKlass:
    out << "GmiCutKlass"; break;
  case BranchCutKlass:
    out << "BranchCutKlass"; break;
  case UnknownKlass:
    out << "UnknownKlass"; break;
  default:
    out << "unexpected CutInfoKlass"; break;
  }
  return out;
}
bool NodeLog::isBranch() const{
  return br_var >= 0;
}

NodeLog::NodeLog()
  : d_nid(-1)
  , d_parent(NULL)
  , d_tl(NULL)
  , d_cuts()
  , d_rowIdsSelected()
  , stat(Open)
  , br_var(-1)
  , br_val(0.0)
  , dn(-1)
  , up(-1)
{}

NodeLog::NodeLog(TreeLog* tl, int node)
  : d_nid(node)
  , d_parent(NULL)
  , d_tl(tl)
  , d_cuts()
  , d_rowIdsSelected()
  , stat(Open)
  , br_var(-1)
  , br_val(0.0)
  , dn(-1)
  , up(-1)
{}

NodeLog::NodeLog(TreeLog* tl, NodeLog* parent, int node)
  : d_nid(node)
  , d_parent(parent)
  , d_tl(tl)
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

int NodeLog::branchVariable() const {
  return br_var;
}
double NodeLog::branchValue() const{
  return br_val;
}
int NodeLog::getNodeId() const {
  return d_nid;
}
int NodeLog::getDownId() const{
  return dn;
}
int NodeLog::getUpId() const{
  return up;
}
void NodeLog::addSelected(int ord, int sel){
  d_rowIdsSelected[ord] = sel;
  cout << "addSelected("<< ord << ", "<< sel << ")" << endl;
}
void NodeLog::applySelected() {
  CutSet::iterator iter = d_cuts.begin(), iend = d_cuts.end(), todelete;
  while(iter != iend){
    CutInfo* curr = *iter;
    int poolOrd = curr->poolOrdinal();
    if(curr->getKlass() == BranchCutKlass){
      // skip
      ++iter;
    }else if(d_rowIdsSelected.find(poolOrd) == d_rowIdsSelected.end()){
      todelete = iter;
      ++iter;
      d_cuts.erase(todelete);
      delete curr;
    }else{
      curr->setRowId( d_rowIdsSelected[poolOrd] );
      ++iter;
    }
  }
}


void NodeLog::addCut(CutInfo* ci){
  Assert(ci != NULL);
  d_cuts.insert(ci);
}

void NodeLog::print(ostream& o) const{
  o << "[n" << getNodeId();
  for(const_iterator iter = begin(), iend = end(); iter != iend; ++iter ){
    CutInfo* cut = *iter;
    o << ", " << cut->poolOrdinal();
    if(cut->getRowId() >= 0){
      o << " " << cut->getRowId();
    }
  }
  o << "]" << std::endl;
}

void NodeLog::closeNode(){
  Assert(stat == Open);
  stat = Closed;
}

void NodeLog::setBranch(int br, double val, int d, int u){
  Assert(stat == Open);
  br_var = br;
  br_val = val;
  dn = d;
  up = u;
  stat = Branched;
}

TreeLog::TreeLog()
  : next_exec_ord(0)
  , d_toNode()
  , d_branches()
  , d_numCuts(0)
  , d_active(false)
{
  clear();
}

int TreeLog::getRootId() const{
  return 1;
}

void TreeLog::clear(){
  next_exec_ord = 0;
  d_toNode.clear();
  d_branches.purge();

  d_numCuts = 0;

  // add root

  d_toNode.insert(make_pair(getRootId(), NodeLog(this, getRootId())));
}

void TreeLog::addCut(){ d_numCuts++; }
uint32_t TreeLog::cutCount() const { return d_numCuts; }
void TreeLog::logBranch(uint32_t x){
  d_branches.add(x);
}
uint32_t TreeLog::numBranches(uint32_t x){
  return d_branches.count(x);
}

void TreeLog::branch(int nid, int br, double val, int dn, int up){
  NodeLog& nl = getNode(nid);
  nl.setBranch(br, val, dn, up);

  d_toNode.insert(make_pair(dn, NodeLog(this, &nl, dn)));
  d_toNode.insert(make_pair(up, NodeLog(this, &nl, up)));
}

void TreeLog::close(int nid){
  NodeLog& nl = getNode(nid);
  nl.closeNode();
}



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


void DenseVector::purge() {
  lhs.purge();
  rhs = Rational(0);
}


BranchCutInfo::BranchCutInfo(int execOrd, int br, Kind dir, double val)
  : CutInfo(BranchCutKlass, execOrd, 0)
{
  d_cutVec.setup(1);
  d_cutVec.inds[1] = br;
  d_cutVec.coeffs[1] = +1.0;
  d_cutRhs = val;
  d_cutType = dir;
}

void TreeLog::printBranchInfo(ostream& os) const{
  uint32_t total = 0;
  DenseMultiset::const_iterator iter = d_branches.begin(),  iend = d_branches.end();
  for(; iter != iend; ++iter){
    uint32_t el = *iter;
    total += el;
  }
  os << "printBranchInfo() : " << total << endl;
  iter = d_branches.begin(),  iend = d_branches.end();
  for(; iter != iend; ++iter){
    uint32_t el = *iter;
    os << "["<<el <<", " << d_branches.count(el) << "]";
  }
  os << endl;
}


void DenseVector::print(std::ostream& os) const {
  os << rhs << " + ";
  print(os, lhs);
}
void DenseVector::print(ostream& out, const DenseMap<Rational>& v){
  out << "[DenseVec len " <<  v.size();
  DenseMap<Rational>::const_iterator iter, end;
  for(iter = v.begin(), end = v.end(); iter != end; ++iter){
    ArithVar x = *iter;
    out << ", "<< x << " " << v[x];
  }
  out << "]";
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
