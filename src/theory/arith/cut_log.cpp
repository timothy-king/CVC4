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
  , N(-1)
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

bool NodeLog::isBranch() const{
  return br_var >= 0;
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

int NodeLog::branchVariable() const {
  return br_var;
}
double NodeLog::branchValue() const{
  return br_val;
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
  : next_exec_ord(0)
  , d_toNode()
  , d_branches()
  , d_numCuts(0)
  , d_active(false)
{
  clear();
}

void TreeLog::clear(){
  next_exec_ord = 0;
  d_toNode.clear();
  d_branches.purge();

  d_numCuts = 0;

  // add root
  int rid = 1;
  d_toNode.insert(make_pair(rid, NodeLog(rid)));
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



}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
