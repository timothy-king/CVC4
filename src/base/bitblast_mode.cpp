/*********************                                                        */
/*! \file bitblast_mode.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitblast modes for bit-vector solver.
 **
 ** Bitblast modes for bit-vector solver.
 **/

#include "base/bitblast_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, theory::bv::BitblastMode mode) {
  switch(mode) {
  case theory::bv::BITBLAST_MODE_LAZY:
    out << "BITBLAST_MODE_LAZY"; 
    break;
  case theory::bv::BITBLAST_MODE_EAGER:
    out << "BITBLAST_MODE_EAGER";
    break;
  default:
    out << "BitblastMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

std::ostream& operator<<(std::ostream& out, theory::bv::BvSlicerMode mode) {
  switch(mode) {
  case theory::bv::BITVECTOR_SLICER_ON:
    out << "BITVECTOR_SLICER_ON"; 
    break;
  case theory::bv::BITVECTOR_SLICER_OFF:
    out << "BITVECTOR_SLICER_OFF";
    break;
  case theory::bv::BITVECTOR_SLICER_AUTO:
    out << "BITVECTOR_SLICER_AUTO";
    break;
  default:
    out << "BvSlicerMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}


}/* CVC4 namespace */
