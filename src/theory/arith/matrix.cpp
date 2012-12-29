/*********************                                                        */
/*! \file matrix.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/matrix.h"

using namespace std;
namespace CVC4 {
namespace theory {
namespace arith {

void NoEffectCCCB::update(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn) {}
void NoEffectCCCB::swap(ArithVar basic, ArithVar nb, int nbSgn){}
bool NoEffectCCCB::canUseRow(RowIndex ridx) const { return false; }

void Tableau::pivot(ArithVar oldBasic, ArithVar newBasic, CoefficientChangeCallback& cb){
  Assert(isBasic(oldBasic));
  Assert(!isBasic(newBasic));
  Assert(d_mergeBuffer.empty());

  Debug("tableau") << "Tableau::pivot(" <<  oldBasic <<", " << newBasic <<")"  << endl;

  RowIndex ridx = basicToRowIndex(oldBasic);

  rowPivot(oldBasic, newBasic, cb);
  Assert(ridx == basicToRowIndex(newBasic));

  loadRowIntoBuffer(ridx);

  ColIterator colIter = colIterator(newBasic);
  while(!colIter.atEnd()){
    EntryID id = colIter.getID();
    Entry& entry = d_entries.get(id);

    ++colIter; //needs to be incremented before the variable is removed
    if(entry.getRowIndex() == ridx){ continue; }

    RowIndex to = entry.getRowIndex();
    Rational coeff = entry.getCoefficient();
    if(cb.canUseRow(to)){
      rowPlusBufferTimesConstant(to, coeff, cb);
    }else{
      rowPlusBufferTimesConstant(to, coeff);
    }
  }
  clearBuffer();

  //Clear the column for used for this variable

  Assert(d_mergeBuffer.empty());
  Assert(!isBasic(oldBasic));
  Assert(isBasic(newBasic));
  Assert(getColLength(newBasic) == 1);
}

/**
 * Changes basic to newbasic (a variable on the row).
 */
void Tableau::rowPivot(ArithVar basicOld, ArithVar basicNew, CoefficientChangeCallback& cb){
  Assert(isBasic(basicOld));
  Assert(!isBasic(basicNew));

  RowIndex rid = basicToRowIndex(basicOld);

  EntryID newBasicID = findOnRow(rid, basicNew);

  Assert(newBasicID != ENTRYID_SENTINEL);

  Tableau::Entry& newBasicEntry = d_entries.get(newBasicID);
  const Rational& a_rs = newBasicEntry.getCoefficient();
  int a_rs_sgn = a_rs.sgn();
  Rational negInverseA_rs = -(a_rs.inverse());

  for(RowIterator i = basicRowIterator(basicOld); !i.atEnd(); ++i){
    EntryID id = i.getID();
    Tableau::Entry& entry = d_entries.get(id);

    entry.getCoefficient() *=  negInverseA_rs;
  }

  d_basic2RowIndex.remove(basicOld);
  d_basic2RowIndex.set(basicNew, rid);
  d_rowIndex2basic.set(rid, basicNew);

  cb.swap(basicOld, basicNew, a_rs_sgn);
}



void Tableau::addRow(ArithVar basic,
                     const std::vector<Rational>& coefficients,
                     const std::vector<ArithVar>& variables)
{
  Assert(basic < getNumColumns());

  Assert(coefficients.size() == variables.size() );
  Assert(!isBasic(basic));

  RowIndex newRow = Matrix<Rational>::addRow(coefficients, variables);
  addEntry(newRow, basic, Rational(-1));

  Assert(!d_basic2RowIndex.isKey(basic));
  Assert(!d_rowIndex2basic.isKey(newRow));

  d_basic2RowIndex.set(basic, newRow);
  d_rowIndex2basic.set(newRow, basic);


  if(Debug.isOn("matrix")){ printMatrix(); }

  NoEffectCCCB noeffect;
  NoEffectCCCB* nep = &noeffect;
  CoefficientChangeCallback* cccb = static_cast<CoefficientChangeCallback*>(nep);

  vector<Rational>::const_iterator coeffIter = coefficients.begin();
  vector<ArithVar>::const_iterator varsIter = variables.begin();
  vector<ArithVar>::const_iterator varsEnd = variables.end();
  for(; varsIter != varsEnd; ++coeffIter, ++varsIter){
    ArithVar var = *varsIter;

    if(isBasic(var)){
      Rational coeff = *coeffIter;

      RowIndex ri = basicToRowIndex(var);

      loadRowIntoBuffer(ri);
      rowPlusBufferTimesConstant(newRow, coeff, *cccb);
      clearBuffer();
    }
  }

  if(Debug.isOn("matrix")) { printMatrix(); }

  Assert(debugNoZeroCoefficients(newRow));
  Assert(debugMatchingCountsForRow(newRow));
  Assert(getColLength(basic) == 1);
}

void Tableau::removeBasicRow(ArithVar basic){
  RowIndex rid = basicToRowIndex(basic);

  removeRow(rid);
  d_basic2RowIndex.remove(basic);
  d_rowIndex2basic.remove(rid);
  
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
