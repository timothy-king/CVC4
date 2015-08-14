
#include "theory/arith/guard_query_printer.h"
#include "theory/arith/normal_form.h"
#include "theory/rewriter.h"
#include <ext/hash_map>
#include <ext/hash_set>
#include <string>
#include <algorithm>
#include <sstream>

#include <iostream>
#include <stdio.h>


using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

typedef std::vector<Node> NodeVec;
typedef __gnu_cxx::hash_set<Node, NodeHashFunction> NodeSet;
typedef __gnu_cxx::hash_map<Node, string, NodeHashFunction> NameMap;




std::pair<Result::Sat, Node> parseGuardedQuery(const std::string& input, const AssertionPartition& assertions);

NodeVec collectVariables(NodeVec::const_iterator begin, NodeVec::const_iterator end){
  NodeVec vars;
  NodeVec queue;
  NodeSet enqueued; // a set of nodes that have ever been added to queue
  
  for(NodeVec::const_iterator ci = begin; ci != end; ++ci){
    Node curr = *ci;
    if(enqueued.find(curr) == enqueued.end()){
      queue.push_back(curr);
      enqueued.insert(curr);
    }
  }

  while(!queue.empty()){
    Node elem = queue.back();
    queue.pop_back();

    if(elem.getMetaKind() == kind::metakind::VARIABLE){
      vars.push_back(elem);
    }
    
    for(unsigned i = 0, N = elem.getNumChildren(); i < N; ++i){
      Node child = elem[i];
      if(enqueued.find(child) == enqueued.end()){
        queue.push_back(child);
        enqueued.insert(child);
      }
    }
  }
    
  return vars;
}

NameMap queryNames(const NodeVec& vars){
  Assert(((unsigned)vars.size()) == vars.size());
  NameMap names;
  for(unsigned i = 0, N = vars.size(); i < N; ++i){
    Node at_i = vars[i];
    std::stringstream ss;
    ss << "x"<<(i+1);
    names.insert(std::make_pair(at_i, ss.str()));
  }
  return names;
}

//["guard"[[">=""(5+-1*x2)*-1*(5*x2+3*x2)+(2*x2+-1*3*x2)*x1"]["<""x2*x1 + -1*x2*x2 + x1*x1*x2"]][[">=" "3+-1*x1+0*x2"][">=" "4+0*x1+-1*x2"][">=" "2+0*x1+1*x2"][">=" "2+1*x1+0*x2"]]]


void printTerm(std::ostream& os, Node t, const NameMap& nameMap){
  os << "(";

  switch(t.getKind()){
  case kind::PLUS:
  case kind::MULT:
    {
      Node::iterator ti = t.begin(), tend = t.end();
      Assert(ti != tend);
      do{
        printTerm(os, *ti, nameMap);
        ++ti;
        if(ti != tend){
          os << ((t.getKind() == kind::PLUS) ? '+' : '*');
        }
      }while(ti != tend);
    }
    break;
  case kind::VARIABLE:
  case kind::SKOLEM:
    {
      NameMap::const_iterator t_iter = nameMap.find(t);
      if(t_iter != nameMap.end()){
        os << (*t_iter).second;
      } else {
        throw std::exception();
      }
    }
    break;
  case kind::CONST_RATIONAL:
    {
      const Rational& q = t.getConst<Rational>();
      if(q.isIntegral()){
        os << q.getNumerator();
      } else{
        os << q.getNumerator() << "/" << q.getDenominator();
      }
    }
    break;
  default:
    Unhandled("Unhandled kind");
  }
  
  os << ")";
}


void printGuard(std::ostream& os, const NameMap& nameMap, Kind k, Node term){
  Assert(k == kind::LT || k == kind::LEQ || k == kind::GEQ || k == kind::LEQ);
  os << "[";
  switch(k){
  case kind::GT:  os << "\">\"";  break;
  case kind::GEQ: os << "\">=\""; break;
  case kind::LEQ: os << "\"<=\""; break;
  case kind::LT:  os << "\"<\"";  break;
  default:
    Unhandled("Unexpected kind in print guard");    
  }
  
  os << "\"";
  printTerm(os, term, nameMap);  
  os << "\"";
  os << "]";
}

void printLiteral(std::ostream& os, const NameMap& nameMap, Node lit){
  Node rw =  Rewriter::rewrite(lit);
  Comparison cmp = Comparison::parseNormalForm(rw);
  Kind k = cmp.comparisonKind();
  
  switch(k){
  case kind::EQUAL:
  case kind::GT:
  case kind::GEQ:
  case kind::LEQ:
  case kind::LT:
    {
      Polynomial l = cmp.getLeft();
      Polynomial r = cmp.getRight();
      Polynomial d = l - r;
      if(k == kind::EQUAL){
        printGuard(os, nameMap, kind::LEQ, d.getNode());
        printGuard(os, nameMap, kind::GEQ, d.getNode());
      }else{
        printGuard(os, nameMap, k, d.getNode());
      }
    }
    break;
  case kind::CONST_BOOLEAN:
    if(rw.getConst<bool>()){
      Polynomial one = Polynomial::mkOne();
      printGuard(os, nameMap, kind::LEQ, one.getNode());
      break;
    }
    // intentionally fall through on the else case
  case kind::DISTINCT:
  default:
    Unhandled("Unhandled kind in printLiteral.");
    break;
  }
}


void printPolynomials(std::ostream& os, const NameMap& nameMap, NodeVec::const_iterator li, NodeVec::const_iterator lend){
  os << "[";
  for(; li != lend; ++li){
    Node lit = *li;
    printLiteral(os, nameMap, lit);
  }
  os << "]";
}


class IsNonlinearPred {
public:
  IsNonlinearPred(){}

  static inline bool isNonlinear(const Node& lit){
    Node rw = Rewriter::rewrite(lit);
    if(!Comparison::isNormalAtom(lit)){ return false; }
    Comparison cmp = Comparison::parseNormalForm(rw);
    Polynomial left = cmp.getLeft();
    Polynomial right = cmp.getRight();
    return left.isNonlinear() || right.isNonlinear();
  }
  
  bool operator()(const Node& n) const {
    return isNonlinear(n);
  }
};

void produceGuardedQuery(std::ostream& os, const AssertionPartition& assertions){
  NodeVec vars = collectVariables(assertions.begin_first(), assertions.end_second());
  NameMap names = queryNames(vars);

  
  os << "[\"guard\"";
  printPolynomials(os, names, assertions.begin_first(), assertions.end_first());
  printPolynomials(os, names, assertions.begin_second(), assertions.end_second());
  os << "]" << endl;
}


std::pair<Result::Sat, Node> executeGuardedQuery(const AssertionPartition& assertions){
  // write into "cvc4guardfile" the query
  ofstream guardfile;
  guardfile.open ("cvc4guardfile");
  produceGuardedQuery(guardfile, assertions);
  guardfile.close();

  // execute vpl on guardfile
  FILE *in;
  stringstream output;
  char buff[512];
  string cmd("./vpl cvc4guardfile");
  
  if(!(in = popen(cmd.c_str(), "r"))){
    throw exception();
  }
  while(fgets(buff, sizeof(buff), in)!=NULL){
    output << buff;
  }
  pclose(in);

  
  return parseGuardedQuery(output.str(), assertions);
}

std::vector<string> lineByLine(const std::string& input){
  istringstream stream(input);
  string line;
  std::vector<string> lines;
  while (std::getline(stream, line)) {
    Debug("guard") << "lines["<<lines.size()<<"] = "<<'"'<<line<<'"'<< endl;
    lines.push_back(line);
  }
  return lines;
}

std::vector<size_t> tokenizeIndices(const std::string& input){
  std::vector<size_t> indices;

  Unimplemented();
  
  return indices;
}

void appendTokens(NodeBuilder<>& nb, const std::vector<size_t>& ind, NodeVec::const_iterator b, size_t max){
  for(std::vector<size_t>::const_iterator i=ind.begin(), iend=ind.end(); i != iend; ++i){
    size_t currInd = *i;
    Assert(currInd < max);
    Node atInd = *(b+currInd);
    nb << atInd;
  }
}

std::pair<Result::Sat, Node> parseGuardedQuery(const std::string& input, const AssertionPartition& assertions){

  std::vector<string> lines = lineByLine(input);
  std::vector<size_t> nlTokens;
  std::vector<size_t> linTokens;

  Result::Sat result = Result::SAT_UNKNOWN;
  
  if(lines.size() >= 1){
    const string& first = lines[0];
    if(first.compare("[[>= \"-1\"]]") == 0){
      result = Result::UNSAT;
      if(lines.size() >= 3){
        const string& second = lines[1];
        const string& third = lines[2];
        nlTokens = tokenizeIndices(second);
        linTokens = tokenizeIndices(third);
      }else{
        // exactly unsat
        for(size_t i = 0, N =  assertions.size_first(); i<N; ++i){
          nlTokens.push_back(i);
        }
        for(size_t i = 0, N = assertions.size_second(); i<N; ++i){
          linTokens.push_back(i);
        }
      }
    }
  }

  if(result == Result::UNSAT){
    NodeBuilder<> conflictNB(kind::AND);
    appendTokens(conflictNB, nlTokens, assertions.begin_first(), assertions.size_first());
    appendTokens(conflictNB, linTokens, assertions.begin_second(), assertions.size_second());

    Node conflict =
      (conflictNB.getNumChildren() == 0) ?
      NodeManager::currentNM()->mkConst<bool>(true) :
      ((conflictNB.getNumChildren() == 1) ?
       conflictNB[0] : (Node)conflictNB);

    return make_pair(Result::UNSAT, conflict);
  }
  
  return make_pair(Result::SAT_UNKNOWN, Node::null());
}



AssertionPartition partitionNonlinear(const NodeVec& assertions){
  NodeVec partitionedAssertions(assertions);
  NodeVec::iterator nonlinear_end =  std::partition(partitionedAssertions.begin(),
                                                    partitionedAssertions.end(), IsNonlinearPred());

  Debug("guard") << "partitionNonlinear():"
                 << "#nl "  << partitionedAssertions.end() - nonlinear_end
                 << "#lin " << (nonlinear_end <= partitionedAssertions.end()) << endl;
  return AssertionPartition(partitionedAssertions, nonlinear_end);
}


AssertionPartition::AssertionPartition()
  : d_assertions()
  , d_pos(d_assertions.begin())
{}

AssertionPartition::AssertionPartition(const NodeVec& as, NodeVec::iterator p)
  : d_assertions(as)
{
  Assert(as.begin() <= p);
  Assert(p <= as.end());

  d_pos = d_assertions.begin() + (p - as.begin());
  
  Assert(d_assertions.begin() <= d_pos);
  Assert(d_pos <= d_assertions.end());
}

size_t AssertionPartition::size() const { return size(); }

size_t AssertionPartition::size_first() const {
  return end_first() - begin_first();
}

size_t AssertionPartition::size_second() const {
  return end_second() - begin_second();
}

NodeVec::const_iterator AssertionPartition::begin_first() const {
  return begin();
}

NodeVec::const_iterator AssertionPartition::end_first() const {
  return d_pos;
}

NodeVec::const_iterator AssertionPartition::begin_second() const {
  return d_pos;
}

NodeVec::const_iterator AssertionPartition::end_second() const {
  return end();
}

NodeVec::const_iterator AssertionPartition::begin() const {
  return d_assertions.begin();
}
NodeVec::const_iterator AssertionPartition::end() const {
  return d_assertions.end();
}



}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
