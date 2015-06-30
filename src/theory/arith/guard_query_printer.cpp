
#include "theory/arith/guard_query_printer.h"
#include "theory/arith/normal_form.h"
#include "theory/rewriter.h"
#include <ext/hash_map>
#include <ext/hash_set>
#include <string>
#include <algorithm>
#include <sstream>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

typedef std::vector<Node> NodeVec;
typedef __gnu_cxx::hash_set<Node, NodeHashFunction> NodeSet;
typedef __gnu_cxx::hash_map<Node, string, NodeHashFunction> NameMap;


NodeVec collectVariables(const NodeVec& heads){
  NodeVec vars;
  NodeVec queue;
  NodeSet enqueued; // a set of nodes that have ever been added to queue
  
  for(NodeVec::const_iterator ci = heads.begin(), cend = heads.end(); ci != cend; ++ci){
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
    if(nameMap.find(t) != nameMap.end()){
      os << (*nameMap.find(t)).second;
    } else {
      throw std::exception();
    }
    break;
  case kind::CONST_RATIONAL:
    {
      const Rational& q = t.getConst<Rational>();
      if(q.isIntegral()){
        os << q;
      } else{
        Unhandled("non-integral rational");
      }
    }
    break;
  default:
    Unhandled("Unhandled kind");
  }
  
  os << ")";
}


void printGuard(std::ostream& os, Kind k, const Polynomial& p, const NameMap& nameMap){
  Assert(k == kind::LT || k == kind::LEQ);
  os << "[";
  if(k == kind::GT){
    os << "\">\"";
  }else if(k == kind::GEQ){
    os << "\">=\"";
  } else {
    Unhandled("Unexpected kind in print guard");
  }
  os << "\"";

  Integer den = p.denominatorLCM();
  Polynomial scaled = p*Rational(den);

  printTerm(os, scaled.getNode(), nameMap);
  
  os << "\"";
  os << "]";
}

void printLiteral(std::ostream& os, Node lit, const NameMap& nameMap){
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
      if(k == kind::LT || k == kind::LEQ){
        d = -d;
        k = (k == kind::LT) ? kind::GT : kind::GEQ;
      }
      if(k == kind::EQUAL){
        printGuard(os, kind::LEQ, d, nameMap);
        printGuard(os, kind::LEQ, -d, nameMap);
      }else{
        printGuard(os, k, d, nameMap);
      }
    }
    break;
  case kind::CONST_BOOLEAN:
    if(rw.getConst<bool>()){
      Polynomial one = Polynomial::mkOne();
      printGuard(os, kind::LEQ, one, nameMap);
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
    printLiteral(os, lit, nameMap);
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

void produceGuardedQuery(std::ostream& os, const NodeVec& assertions){
  NodeVec vars = collectVariables(assertions);
  NameMap names = queryNames(vars);

  NodeVec partitionedAssertions(assertions);
  NodeVec::iterator nonlinear_end =  std::partition(partitionedAssertions.begin(), partitionedAssertions.end(), IsNonlinearPred());

  cerr << assertions.size() << " " << partitionedAssertions.size() << " " << (nonlinear_end - partitionedAssertions.begin())
       << " " << partitionedAssertions.end() - nonlinear_end << endl;
  
  os << "[\"guard\" ";
  printPolynomials(os, names, partitionedAssertions.begin(), nonlinear_end);
  printPolynomials(os, names, nonlinear_end, partitionedAssertions.end());
  os << "]" << endl;
    
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
