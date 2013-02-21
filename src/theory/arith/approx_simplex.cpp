#include <glpk.h>
#include "theory/arith/approx_simplex.h"

namespace CVC4 {
namespace theory {
namespace arith {

const double ApproximateSimplex::SMALL_FIXED_DELTA = .0000001;
const double ApproximateSimplex::TOLERENCE = 1 + .0000001;

bool ApproximateSimplex::roughlyEqual(double a, double b){
  if (a == 0){
    return -SMALL_FIXED_DELTA <= b && b <= SMALL_FIXED_DELTA;
  }else if (b == 0){
    return -SMALL_FIXED_DELTA <= a && a <= SMALL_FIXED_DELTA;
  }else{
    return b/a <= TOLERENCE && a/b <= TOLERENCE;
  }
}

void ApproximateSimplex::approximateRelaxation(LinearEqualityModule& linEq){
  const Tableau& tableau = linEq.getTableau();
  const ArithVariables& vars = linEq.getVariables();

  uint32_t numRows =  tableau.getNumRows();
  uint32_t numCols =  tableau.getNumColumns();

  // constructs a glpk problem instance
  // the glpk row variables will be in <-> with our basic variables
  //  the row variables with index i == Tableau row index <-> basic variable
  // the column variables will be in <-> with our non-basic variables
  //  the col variable with index i == arith var i
  //  (we will have empty columns for basic variables, but who cares)


  glp_prob* lp = glp_create_prob();
  glp_set_prob_name(lp, "ApproximateSimplex::approximateFindModel");
  glp_set_obj_dir(lp, GLP_MAX);
  glp_add_rows(lp, numRows);

  for(ArithVar v = 0; v < numCols; ++v){
    int type;
    double lb = 0;
    double ub = 0;
    if(vars.hasUpperBound(v) && vars.hasLowerBound(v)){
      if(vars.boundsAreEqual(v)){
        type = GLP_FX;
      }else{
        type = GLP_DB;
      }
      lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
      ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
    }else if(vars.hasUpperBound(v) && !vars.hasLowerBound(v)){
      type = GLP_UP;
      ub = vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
    }else if(!vars.hasUpperBound(v) && vars.hasLowerBound(v)){
      type = GLP_LO;
      lb = vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
    }else{
      type = GLP_FR;
    }

    if(tableau.isBasic(v)){
      glp_set_row_bnds(lp, v, type, lb, ub);
    }else{
      glp_set_col_bnds(lp, v, type, lb, ub);

      //const Rational& focusC = focusCoefficient(v);
      //if(!focusC.isZero()){
      //glp_set_obj_coef(lp, v, focusC.getDouble());
      //}
    }
  }

  // The entries of the of the tableau -> entries in the glpk matrix
  uint32_t numEntries = tableau.getNumEntriesInTableau();
  int* ia = new int[numEntries];
  int* ja = new int[numEntries];
  double* ar = new double[numEntries];
  int k = 0;
  for(ArithVar v = 0; v < numCols; ++v){
    if(!tableau.isBasic(v)){
      for(Tableau::ColIterator i=tableau.getColumn(v).begin(); !i.atEnd(); ++i){
        const Tableau::Entry& e=*i;
        ia[k] = e.getRowIndex();
        ja[k] = e.getColVar();
        ar[k] = e.getCoefficient().getDouble();
        k++;
        Assert(k <= numEntries);
      }
    }
  }
  glp_load_matrix(lp, numEntries, ia, ja, ar);

  // Explicitly disable presolving
  // We need the basis thus the presolver must be off!
  // This is default, but this is just being cautious.
  glp_smcp parm;
  glp_init_smcp(&parm);
  parm.presolve = GLP_OFF;
  parm.meth = GLP_PRIMAL;
  parm.pricing = GLP_PT_PSE;
#warning "Turn this off, before checking into trunk"
  parm.msg_lev = GLP_MSG_ALL;

  glp_simplex(lp, &parm);

  DenseSet newBasis;
  // newBasis \cup newValue.keys() == [0,numCols)
  DenseMap<DeltaRational> newValues;
  for(ArithVar v = 0; v < numCols; ++v){
    bool isBasic = tableau.isBasic(v);
    RowIndex ri = isBasic ? tableau.basicToRowIndex(v) : 0;
    int status = isBasic ? glp_get_row_stat(lp, ri) : glp_get_col_stat(lp, v);
    switch(status){
    case GLP_BS:
      newBasis.add(v);
      break;
    case GLP_NL:
    case GLP_NS:
      newValues.set(v, vars.getLowerBound(v));
      break;
    case GLP_NU:
      newValues.set(v, vars.getUpperBound(v));
      break;
    default:
      {
        double newAssign = isBasic ? glp_get_row_prim(lp, ri) :  glp_get_col_prim(lp, v);
        const DeltaRational& oldAssign = vars.getAssignment(v);
        if(roughlyEqual(newAssign, oldAssign.approx(SMALL_FIXED_DELTA))){
          newValues.set(v, vars.getAssignment(v));
        }else{
          DeltaRational proposal = Rational::fromDouble(newAssign);
          if(proposal < vars.getLowerBound(v)){
            proposal = vars.getLowerBound(v);
          }else if(proposal > vars.getUpperBound(v)){
            proposal = vars.getUpperBound(v);
          }
          newValues.set(v, proposal);
        }
        break;
      }
    }
  }

  delete[] ia;
  delete[] ja;
  delete[] ar;
  glp_delete_prob(lp);

  linEq.forceNewBasis(newBasis);
  linEq.updateMany(newValues);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
