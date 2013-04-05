extern "C" {
#include <glpk.h>
}
#include "theory/arith/approx_simplex.h"
#include "theory/arith/normal_form.h"
#include <math.h>
#include <cmath>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {


bool ApproximateSimplex::roughlyEqual(double a, double b){
  if (a == 0){
    return -SMALL_FIXED_DELTA <= b && b <= SMALL_FIXED_DELTA;
  }else if (b == 0){
    return -SMALL_FIXED_DELTA <= a && a <= SMALL_FIXED_DELTA;
  }else{
    return std::abs(b/a) <= TOLERENCE && std::abs(a/b) <= TOLERENCE;
  }
}

Rational cfe(const vector<Integer>& exp){
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

Rational continuedFractionExpansion(const Rational& q, int depth){
  //cout << "cfe: " << q << endl;
  vector<Integer> mods;
  if(!q.isZero()){
    Rational carry = q;
    for(int i = 0; i <= depth; ++i){
      Assert(!carry.isZero())
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

  Rational result = cfe(mods);
  //cout << "cfe: " << result << endl;

  return result;
}

class ApproxGLPK : public ApproximateSimplex {
private:
  glp_prob* d_prob;
  const ArithVariables& d_vars;

  DenseMap<int> d_colIndices;
  DenseMap<int> d_rowIndices;


  int d_instanceID;

  bool d_solvedRelaxation;
  bool d_solvedMIP;

public:
  ApproxGLPK(const ArithVariables& vars);
  ~ApproxGLPK();

  ApproxResult solveRelaxation(unsigned pivotLimit);
  Solution extractRelaxation() const {
    return extractSolution(false);
  }

  ApproxResult solveMIP(unsigned pivotLimit);
  Solution extractMIP() const{
    return extractSolution(true);
  }

private:
  Solution extractSolution(bool mip) const;
};

const double ApproximateSimplex::SMALL_FIXED_DELTA = .000000001;
const double ApproximateSimplex::TOLERENCE = 1 + .000000001;

ApproximateSimplex* ApproximateSimplex::mkApproximateSimplexSolver(const ArithVariables& vars){
  return new ApproxGLPK(vars);
}

ApproxGLPK::ApproxGLPK(const ArithVariables& avars) :
  d_vars(avars), d_solvedRelaxation(false), d_solvedMIP(false)
{
  static int instance = 0;
  ++instance;
  d_instanceID = instance;

  d_prob = glp_create_prob();
  glp_set_prob_name(d_prob, "ApproximateSimplex::approximateFindModel");
  glp_set_obj_dir(d_prob, GLP_MAX);

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

      ++entryCounter;
      ia[entryCounter] = rowIndex;
      ja[entryCounter] = colIndex;
      ar[entryCounter] = constant.getValue().getDouble();
    }
  }
  glp_load_matrix(d_prob, numEntries, ia, ja, ar);

  delete[] ia;
  delete[] ja;
  delete[] ar;
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

static void printGLPKStatus(int status){
  switch(status){
  case GLP_OPT:
    cout << "GLP_OPT" << endl;
    break;
  case GLP_FEAS:
    cout << "GLP_FEAS" << endl;
    break;
  case GLP_INFEAS:
    cout << "GLP_INFEAS" << endl;
    break;
  case GLP_NOFEAS:
    cout << "GLP_NOFEAS" << endl;
    break;
  case GLP_UNBND:
    cout << "GLP_UNBND" << endl;
    break;
  case GLP_UNDEF:
    cout << "GLP_UNDEF" << endl;
    break;
  default:
    cout << "Status unknown" << endl;
    break;
  }
}

ApproxGLPK::~ApproxGLPK(){
  glp_delete_prob(d_prob);
}

// void ApproximateSimplex::encodeOriginalMatrix(void* v, const ArithVariables& vars, DenseMap<int>& colIndices, DenseMap<int>& rowIndices){
//   glp_prob* prob = (glp_prob*)v;
//   int numRows = 0;
//   int numCols = 0;

//   // Assign each variable to a row and column variable as it appears in the input
//   for(ArithVariables::var_iterator vi = vars.var_begin(), vi_end = vars.var_end(); vi != vi_end; ++vi){
//     ArithVar v = *vi;

//     if(vars.isSlack(v)){
//       ++numRows;
//       rowIndices.set(v, numRows);
//     }else{
//       ++numCols;
//       colIndices.set(v, numCols);
//     }
//   }
//   glp_add_rows(prob, numRows);
//   glp_add_cols(prob, numCols);

//   // Assign the upper/lower bounds and types to each variable
//   for(ArithVariables::var_iterator vi = vars.var_begin(), vi_end = vars.var_end(); vi != vi_end; ++vi){
//     ArithVar v = *vi;

//     int type;
//     double lb = 0.0;
//     double ub = 0.0;
//     if(vars.hasUpperBound(v) && vars.hasLowerBound(v)){
//       if(vars.boundsAreEqual(v)){
//         type = GLP_FX;
//       }else{
//         type = GLP_DB;
//       }
//       lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
//       ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
//     }else if(vars.hasUpperBound(v) && !vars.hasLowerBound(v)){
//       type = GLP_UP;
//       ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
//     }else if(!vars.hasUpperBound(v) && vars.hasLowerBound(v)){
//       type = GLP_LO;
//       lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
//     }else{
//       type = GLP_FR;
//     }

//     if(vars.isSlack(v)){
//       int rowIndex = rowIndices[v];
//       glp_set_row_bnds(prob, rowIndex, type, lb, ub);
//     }else{
//       int colIndex = colIndices[v];

//       if(mip){
//         int kind = vars.isInteger(v) ? GLP_IV : GLP_CV;
//         glp_set_col_kind(prob, colIndex, kind);
//         glp_set_obj_coef(prob, colIndex, -1.0);
//       }
//     }
//   }

//   // Count the number of entries
//   int numEntries = 0;
//   for(DenseMap<int>::const_iterator i = rowIndices.begin(), i_end = rowIndices.end(); i != i_end; ++i){
//     ArithVar v = *i;
//     Polynomial p = Polynomial::parsePolynomial(vars.asNode(v));
//     for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
//       ++numEntries;
//     }
//   }

//   int* ia = new int[numEntries+1];
//   int* ja = new int[numEntries+1];
//   double* ar = new double[numEntries+1];

//   int entryCounter = 0;
//   for(DenseMap<int>::const_iterator i = rowIndices.begin(), i_end = rowIndices.end(); i != i_end; ++i){
//     ArithVar v = *i;
//     int rowIndex = rowIndices[v];

//     Polynomial p = Polynomial::parsePolynomial(vars.asNode(v));

//     for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){

//       const Monomial& mono = *i;
//       const Constant& constant = mono.getConstant();
//       const VarList& variable = mono.getVarList();

//       Node n = variable.getNode();

//       Assert(d_partialModel.hasArithVar(n));
//       ArithVar av = vars.asArithVar(n);
//       int colIndex = colIndices[av];

//       ++entryCounter;
//       ia[entryCounter] = rowIndex;
//       ja[entryCounter] = colIndex;
//       ar[entryCounter] = constant.getValue().getDouble();
//     }
//   }
//   glp_load_matrix(prob, numEntries, ia, ja, ar);

//   delete[] ia;
//   delete[] ja;
//   delete[] ar;
// }



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
    //cout << "assignment " << vi << endl;

    switch(status){
    case GLP_BS:
      //cout << "basic" << endl;
      newBasis.add(vi);
      break;
    case GLP_NL:
    case GLP_NS:
      if(!mip){
        //cout << "non-basic lb" << endl;
        newValues.set(vi, d_vars.getLowerBound(vi));
        break;
      }// intentionally fall through otherwise
    case GLP_NU:
      if(!mip){
        // cout << "non-basic ub" << endl;
        newValues.set(vi, d_vars.getUpperBound(vi));
        break;
      }// intentionally fall through otherwise
    default:
      {
        // cout << "non-basic other" << endl;

        double newAssign =
          mip ?
            (isSlack ? glp_mip_row_val(d_prob, glpk_index) :  glp_mip_col_val(d_prob, glpk_index))
          : (isSlack ? glp_get_row_prim(d_prob, glpk_index) :  glp_get_col_prim(d_prob, glpk_index));
        const DeltaRational& oldAssign = d_vars.getAssignment(vi);


        if(d_vars.hasLowerBound(vi) &&
           roughlyEqual(newAssign, d_vars.getLowerBound(vi).approx(SMALL_FIXED_DELTA))){
          //cout << "  to lb" << endl;

          newValues.set(vi, d_vars.getLowerBound(vi));
        }else if(d_vars.hasUpperBound(vi) &&
           roughlyEqual(newAssign, d_vars.getUpperBound(vi).approx(SMALL_FIXED_DELTA))){
          newValues.set(vi, d_vars.getUpperBound(vi));
          // cout << "  to ub" << endl;
        }else{

          double rounded = round(newAssign);
          if(roughlyEqual(newAssign, rounded)){
            // cout << "roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
            newAssign = rounded;
          }else{
            // cout << "not roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
          }

          Rational fromD = Rational::fromDouble(newAssign);
          Rational approx = continuedFractionExpansion(fromD, 10);
          DeltaRational proposal = approx;


          if(roughlyEqual(newAssign, oldAssign.approx(SMALL_FIXED_DELTA))){
            // cout << "  to prev value" << newAssign << " " << oldAssign << endl;
            proposal = d_vars.getAssignment(vi);
          }


          if(d_vars.strictlyLessThanLowerBound(vi, proposal)){
            //cout << "  round to lb " << d_vars.getLowerBound(vi) << endl;
            proposal = d_vars.getLowerBound(vi);
          }else if(d_vars.strictlyGreaterThanUpperBound(vi, proposal)){
            //cout << "  round to ub " << d_vars.getUpperBound(vi) << endl;
            proposal = d_vars.getUpperBound(vi);
          }else{
            //cout << "  use proposal" << proposal << " " << oldAssign  << endl;
          }
          newValues.set(vi, proposal);
        }
        break;
      }
    }
  }
  return sol;
}

ApproximateSimplex::ApproxResult ApproxGLPK::solveRelaxation(unsigned pivotLimit){
  Assert(!d_solvedRelaxation);

  glp_smcp parm;
  glp_init_smcp(&parm);
  parm.presolve = GLP_OFF;
  parm.meth = GLP_PRIMAL;
  parm.pricing = GLP_PT_PSE;
#warning "Turn this off, before checking into trunk"
  //parm.msg_lev = GLP_MSG_ALL;
  parm.msg_lev = GLP_MSG_OFF;

  int res = glp_simplex(d_prob, &parm);

  switch(res){
  case 0:
    {
      int status = glp_get_status(d_prob);
      //printGLPKStatus(status);
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

ApproximateSimplex::ApproxResult ApproxGLPK::solveMIP(unsigned pivotLimit){
  Assert(d_solvedRelaxation);

  // Explicitly disable presolving
  // We need the basis thus the presolver must be off!
  // This is default, but this is just being cautious.
  glp_iocp parm;
  glp_init_iocp(&parm);
  parm.presolve = GLP_OFF;
  parm.pp_tech = GLP_PP_NONE;
  parm.fp_heur = GLP_ON;
  parm.gmi_cuts = GLP_ON;
  parm.mir_cuts = GLP_ON;
  parm.cov_cuts = GLP_ON;
  parm.tm_lim = 20000;
  parm.presolve = GLP_OFF;
#warning "Turn this off, before checking into trunk"
  parm.msg_lev = GLP_MSG_ALL;
  parm.msg_lev = GLP_MSG_OFF;

  //cout << "glpk int " << d_instanceID << endl;
  int res = glp_intopt(d_prob, &parm);

  // cout << "glpk int " << d_instanceID << " result " << res << endl;
  //printGLPKStatus(glp_get_status(d_prob));

  switch(res){
  case 0:
    {
      int status = glp_mip_status(d_prob);
      //printGLPKStatus(status);
      switch(status){
      case GLP_OPT:
      case GLP_FEAS:
        d_solvedMIP = true;
        return ApproxSat;
      case GLP_NOFEAS:
        d_solvedMIP = true;
        return ApproxUnsat;
        // GLP_UNDEF ?
      default:
        return ApproxError;
      }
    }
  default:
    return ApproxError;
  }
}

// void ApproximateSimplex::approximateRelaxation(LinearEqualityModule& linEq){
//   const Tableau& tableau = linEq.getTableau();
//   const ArithVariables& vars = linEq.getVariables();

//   static int instance = 0;
//   ++instance;

//   uint32_t numRows =  tableau.getNumRows();
//   uint32_t numCols =  tableau.getNumColumns();

//   cout << "real approx!" << instance <<
//     " numRows " << numRows <<
//     " numCols " << numCols<< endl;

//   // constructs a glpk problem instance
//   // the glpk row variables will be in <-> with our basic variables
//   //  the row variables with index i == Tableau row index <-> basic variable
//   // the column variables will be in <-> with our non-basic variables
//   //  the col variable with index i == arith var i
//   //  (we will have empty columns for basic variables, but who cares)


//   glp_prob* lp = glp_create_prob();
//   glp_set_prob_name(lp, "ApproximateSimplex::approximateFindModel");
//   glp_set_obj_dir(lp, GLP_MAX);

//   DenseMap<int> colIndices, rowIndices;

//   encodeOriginalMatrix(lp, false, vars, colIndices, rowIndices);

//   // for(ArithVariables::var_iterator vi = vars.var_begin(), vi_end = vars.var_end(); vi != vi_end; ++vi){
//   //   ArithVar v = *vi;
//   //   int type;
//   //   double lb = 0.0;
//   //   double ub = 0.0;
//   //   if(vars.hasUpperBound(v) && vars.hasLowerBound(v)){
//   //     if(vars.boundsAreEqual(v)){
//   //       type = GLP_FX;
//   //     }else{
//   //       type = GLP_DB;
//   //     }
//   //     lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
//   //     ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
//   //   }else if(vars.hasUpperBound(v) && !vars.hasLowerBound(v)){
//   //     type = GLP_UP;
//   //     ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
//   //   }else if(!vars.hasUpperBound(v) && vars.hasLowerBound(v)){
//   //     type = GLP_LO;
//   //     lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
//   //   }else{
//   //     type = GLP_FR;
//   //   }

//   //   if(tableau.isBasic(v)){
//   //     RowIndex ri = tableau.basicToRowIndex(v);
//   //     glp_set_row_bnds(lp, ri+1, type, lb, ub);
//   //   }else{
//   //     glp_set_col_bnds(lp, v+1, type, lb, ub);
//   //     //const Rational& focusC = focusCoefficient(v);
//   //     //if(!focusC.isZero()){
//   //     //glp_set_obj_coef(lp, v, focusC.getDouble());
//   //     //}
//   //   }
//   // }

//   // // The entries of the of the tableau -> entries in the glpk matrix
//   // uint32_t numEntries = tableau.getNumEntriesInTableau();
//   // int* ia = new int[numEntries+1];
//   // int* ja = new int[numEntries+1];
//   // double* ar = new double[numEntries+1];
//   // int k = 0;
//   // for(ArithVar v = 0; v < numCols; ++v){
//   //   if(!tableau.isBasic(v)){
//   //     for(Tableau::ColIterator i=tableau.getColumn(v).begin(); !i.atEnd(); ++i){
//   //       const Tableau::Entry& e=*i;
//   //       k++;
//   //       ia[k] = 1+ e.getRowIndex();
//   //       ja[k] = 1+ e.getColVar();
//   //       ar[k] = e.getCoefficient().getDouble();
//   //       Assert(k <= numEntries);
//   //     }
//   //   }
//   // }
//   // glp_load_matrix(lp, k, ia, ja, ar);

//   // Explicitly disable presolving
//   // We need the basis thus the presolver must be off!
//   // This is default, but this is just being cautious.
//   glp_smcp parm;
//   glp_init_smcp(&parm);
//   parm.presolve = GLP_OFF;
//   parm.meth = GLP_PRIMAL;
//   parm.pricing = GLP_PT_PSE;
// #warning "Turn this off, before checking into trunk"
//   parm.msg_lev = GLP_MSG_ALL;

//   int res = glp_simplex(lp, &parm);

//   cout << "real approx " << instance << " result " << res << endl;
//   printGLPKStatus(glp_get_status(lp));

//   DenseSet newBasis;
//   // newBasis \cup newValue.keys() == initialized variables
//   DenseMap<DeltaRational> newValues;

//   extractSolution(lp, false, vars, colIndices, rowIndices, newBasis,  newValues);

//   // for(ArithVariables::var_iterator vi = vars.var_begin(), vi_end = vars.var_end(); vi != vi_end; ++vi){
//   //   ArithVar v = *vi;
//   //   bool isBasic = tableau.isBasic(v);
//   //   RowIndex ri = isBasic ? tableau.basicToRowIndex(v) : 0;
//   //   int status = isBasic ? glp_get_row_stat(lp, ri+1) : glp_get_col_stat(lp, v+1);
//   //   switch(status){
//   //   case GLP_BS:
//   //     newBasis.add(v);
//   //     break;
//   //   case GLP_NL:
//   //   case GLP_NS:
//   //     newValues.set(v, vars.getLowerBound(v));
//   //     break;
//   //   case GLP_NU:
//   //     newValues.set(v, vars.getUpperBound(v));
//   //     break;
//   //   default:
//   //     {
//   //       double newAssign = isBasic ? glp_get_row_prim(lp, ri+1) :  glp_get_col_prim(lp, v+1);
//   //       const DeltaRational& oldAssign = vars.getAssignment(v);
//   //       // if(roughlyEqual(newAssign, oldAssign.approx(SMALL_FIXED_DELTA))){
//   //       //   newValues.set(v, vars.getAssignment(v));
//   //       // }else{
//   //         DeltaRational proposal = Rational::fromDouble(newAssign);
//   //         if(vars.strictlyLessThanLowerBound(v, proposal)){
//   //           proposal = vars.getLowerBound(v);
//   //         }else if(vars.strictlyGreaterThanUpperBound(v, proposal)){
//   //           proposal = vars.getUpperBound(v);
//   //         }
//   //         newValues.set(v, proposal);
//   //         //}
//   //       break;
//   //     }
//   //   }
//   // }

//   // delete[] ia;
//   // delete[] ja;
//   // delete[] ar;
//   glp_delete_prob(lp);

//   linEq.forceNewBasis(newBasis);
//   linEq.updateMany(newValues);
// }

// void ApproximateSimplex::approximateIntegers(LinearEqualityModule& linEq){
//   const Tableau& tableau = linEq.getTableau();
//   const ArithVariables& vars = linEq.getVariables();

//   static int instance = 0;
//   ++instance;

//   uint32_t numRows =  tableau.getNumRows();
//   uint32_t numCols =  tableau.getNumColumns();

//   cout << "int approx!" << instance <<
//     " numRows " << numRows <<
//     " numCols " << numCols<< endl;

//   // constructs a glpk problem instance
//   // the glpk row variables will be in <-> with our basic variables
//   //  the row variables with index i == Tableau row index <-> basic variable
//   // the column variables will be in <-> with our non-basic variables
//   //  the col variable with index i == arith var i
//   //  (we will have empty columns for basic variables, but who cares)


//   glp_prob* mip = glp_create_prob();
//   glp_set_prob_name(mip, "ApproximateSimplex::approximateIntegers");
//   glp_set_obj_dir(mip, GLP_MAX);


//   // for(ArithVariables::var_iterator vi = vars.var_begin(), vi_end = vars.var_end(); vi != vi_end; ++vi){
//   //   ArithVar v = *vi;
//   //   int type;
//   //   double lb = 0.0;
//   //   double ub = 0.0;
//   //   if(vars.hasUpperBound(v) && vars.hasLowerBound(v)){
//   //     if(vars.boundsAreEqual(v)){
//   //       type = GLP_FX;
//   //     }else{
//   //       type = GLP_DB;
//   //     }
//   //     lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
//   //     ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
//   //   }else if(vars.hasUpperBound(v) && !vars.hasLowerBound(v)){
//   //     type = GLP_UP;
//   //     ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
//   //   }else if(!vars.hasUpperBound(v) && vars.hasLowerBound(v)){
//   //     type = GLP_LO;
//   //     lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
//   //   }else{
//   //     type = GLP_FR;
//   //   }

//   //   int kind = vars.isInteger(v) ? GLP_IV : GLP_CV;

//   //   cout << "v " << v << " "  << type << " " << kind << endl;

//   //   glp_set_col_bnds(mip, v+1, type, lb, ub);
//   //   glp_set_col_kind(mip, v+1, kind);
//   //   //const Rational& focusC = focusCoefficient(v);
//   //   //if(!focusC.isZero()){
//   //   //glp_set_obj_coef(mip, v, -1.0);
//   //   //}
//   // }
//   // for(RowIndex ri = 1; ri <= numRows; ri++){
//   //   glp_set_row_bnds(mip, ri, GLP_FX, 0.0, 0.0);
//   // }

//   // // The entries of the of the tableau -> entries in the glpk matrix
//   // uint32_t numEntries = tableau.getNumEntriesInTableau();
//   // int* ia = new int[numEntries+1];
//   // int* ja = new int[numEntries+1];
//   // double* ar = new double[numEntries+1];
//   // int k = 0;
//   // for(ArithVar v = 0; v < numCols; ++v){
//   //   for(Tableau::ColIterator i=tableau.getColumn(v).begin(); !i.atEnd(); ++i){
//   //     const Tableau::Entry& e=*i;
//   //     k++;
//   //     ia[k] = 1+ e.getRowIndex();
//   //     ja[k] = 1+ e.getColVar();
//   //     ar[k] = e.getCoefficient().getDouble();
//   //     Assert(k <= numEntries);
//   //   }
//   // }
//   // glp_load_matrix(mip, k, ia, ja, ar);

//   DenseMap<int> colIndices, rowIndices;
//   encodeOriginalMatrix(mip, true, vars, colIndices, rowIndices);

//   // Explicitly disable presolving
//   // We need the basis thus the presolver must be off!
//   // This is default, but this is just being cautious.
//   glp_iocp parm;
//   glp_init_iocp(&parm);
//   parm.presolve = GLP_OFF;
//   parm.pp_tech = GLP_PP_NONE;
//   //parm.meth = GLP_PRIMAL;
//   parm.fp_heur = GLP_ON;
//   parm.gmi_cuts = GLP_ON;
//   parm.mir_cuts = GLP_ON;
//   parm.cov_cuts = GLP_ON;


//   parm.presolve = GLP_OFF;
//   //parm.pricing = GLP_PT_PSE;
// #warning "Turn this off, before checking into trunk"
//   parm.msg_lev = GLP_MSG_ALL;

//   glp_smcp lpparm;
//   glp_init_smcp(&lpparm);
//   lpparm.presolve = GLP_OFF;
//   lpparm.meth = GLP_PRIMAL;
//   lpparm.presolve = GLP_OFF;
//   lpparm.pricing = GLP_PT_PSE;
// #warning "Turn this off, before checking into trunk"
//   lpparm.msg_lev = GLP_MSG_ALL;

//   int res = glp_simplex(mip, &lpparm);
//   cout << "glpk int " << instance << " result " << res << endl;
//   res = glp_intopt(mip, &parm);

//   cout << "glpk int " << instance << " result " << res << endl;
//   printGLPKStatus(glp_get_status(mip));

//   DenseSet newBasis;
//   // newBasis \cup newValue.keys() == initialized variables
//   DenseMap<DeltaRational> newValues;
//   extractSolution(mip, true, vars, colIndices, rowIndices, newBasis,  newValues);

//   // // newBasis \cup newValue.keys() == initialized variables
//   // DenseMap<DeltaRational> newValues;
//   // for(ArithVariables::var_iterator vi = vars.var_begin(), vi_end = vars.var_end(); vi != vi_end; ++vi){
//   //   ArithVar v = *vi;
//   //   bool isBasic = tableau.isBasic(v);
//   //   if(isBasic){
//   //     double newAssign =  glp_mip_col_val(mip, v+1);

//   //     const DeltaRational& oldAssign = vars.getAssignment(v);

//   //     double rounded = round(newAssign);

//   //     cout << "basic: " << v << " " << vars.isInteger(v) << " " << oldAssign << " " << newAssign << " " << rounded << endl;
//   //     continue;
//   //   }
//   //   //RowIndex ri = isBasic ? tableau.basicToRowIndex(v) : 0;
//   //   //int status = isBasic ? glp_get_row_stat(mip, ri+1) : glp_get_col_stat(mip, v+1);
//   //   int status = glp_get_col_stat(mip, v+1);
//   //   switch(status){
//   //     //case GLP_BS:
//   //     //break;
//   //   case GLP_NL:
//   //   case GLP_NS:
//   //     newValues.set(v, vars.getLowerBound(v));
//   //     break;
//   //   case GLP_NU:
//   //     newValues.set(v, vars.getUpperBound(v));
//   //     break;
//   //   case GLP_BS:
//   //   default:
//   //     {
//   //       //double newAssign = isBasic ? glp_get_row_prim(mip, ri+1) :  glp_get_col_prim(mip, v+1);
//   //       double newAssign =  glp_mip_col_val(mip, v+1);

//   //       const DeltaRational& oldAssign = vars.getAssignment(v);

//   //       double rounded = round(newAssign);

//   //       cout << "v: " << v << " " << vars.isInteger(v) << " " << oldAssign << " " << newAssign << " " << rounded << endl;

//   //       if(vars.isInteger(v)){
//   //         newAssign = rounded;
//   //         cout << "rounding " << newAssign << endl;
//   //       }

//   //       // if(roughlyEqual(newAssign, oldAssign.approx(SMALL_FIXED_DELTA))){
//   //       //   newValues.set(v, vars.getAssignment(v));
//   //       //   cout << "approximately old " << newAssign << endl;
//   //       // }else{
//   //         DeltaRational proposal = Rational::fromDouble(newAssign);
//   //         if(vars.strictlyLessThanLowerBound(v, proposal)){
//   //           cout << "violated lb" << endl;
//   //           proposal = vars.getLowerBound(v);
//   //         }else if(vars.strictlyGreaterThanUpperBound(v, proposal)){
//   //           proposal = vars.getUpperBound(v);
//   //           cout << "violated ub" << endl;
//   //         }
//   //         newValues.set(v, proposal);
//   //         //}
//   //       break;
//   //     }
//   //   }
//   // }

//   // delete[] ia;
//   // delete[] ja;
//   // delete[] ar;
//   //glp_delete_prob(mip);

//   cout << newBasis.size() << " " << numRows << endl;
//   if(newBasis.size()+1 != numRows){
//     exit(1);
//   }

//   DenseSet preimage;

//   int unboundNB = 0;
//   int unboundB = 0;

//   linEq.forceNewBasis(newBasis);
//   linEq.updateMany(newValues);
//   cout << "-------- non-basics ---------" << endl;
//   for(DenseMap<DeltaRational>::const_iterator i = newValues.begin(), i_end = newValues.end(); i != i_end; ++i){
//     ArithVar v = *i;
//     const DeltaRational& val = newValues[v];
//     vars.printModel(v, cout);
//     cout << "  " << val << endl;

//     if(tableau.isBasic(v)){
//       exit(1);
//     }

//     if(!vars.hasEitherBound(v)){
//       ++unboundNB;
//     }

//     preimage.add(v);
//   }

//   cout << "-------- basics ---------" << endl;
//   for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
//     ArithVar v = *i;
//     vars.printModel(v, cout);

//     if(!tableau.isBasic(v)){
//       exit(1);
//     }

//     if(!vars.assignmentIsConsistent(v)){
//       cout << "not consistent : " << v << endl;
//       RowIndex rid = tableau.basicToRowIndex(v);
//       tableau.printRow(rid,cout);
//     }
//     if(!vars.hasEitherBound(v)){
//       ++unboundB;
//     }
//     preimage.add(v);
//   }

//   cout << "Unbound: non-basics(" << unboundNB << ")"
//        << "basics (" << unboundB << ")" << endl;

//   for(ArithVariables::var_iterator i = vars.var_begin(), i_end = vars.var_end(); i != i_end; ++i){
//     ArithVar v = *i;
//     if(!preimage.isMember(v)){
//       cout << v<< endl;
//       exit(1);
//     }
//   }

//   glp_delete_prob(mip);
// }


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
