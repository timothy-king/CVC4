/*********************                                                        */
/*! \file attribute.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief AttributeManager implementation.
 **
 ** AttributeManager implementation.
 **/

#include "expr/attribute.h"
#include "expr/node_value.h"
#include "util/output.h"

#include <utility>

using namespace std;

namespace CVC4 {
namespace expr {
namespace attr {


void AttributeManager::debugHook(int debugFlag) {
  std::ostream& out = Chat();
  out << "AttributeManager::debugHook("<<debugFlag<<")"<< endl;

  if(!d_bools.empty()){
    out << " AM d_bools " << d_bools.size() << endl;
  }
  if(!d_ints.empty()){
    out << " AM d_ints " << d_ints.size() << endl;
  }
  if(!d_tnodes.empty()){
    out << " AM d_tnodes " << d_tnodes.size() << endl;
  }
  if(!d_nodes.empty()){
    out << " AM d_nodes " << d_nodes.size() << endl;
  }
  if(!d_types.empty()){
    out << " AM d_types " << d_types.size() << endl;
  }
  if(!d_strings.empty()){
    out << " AM d_strings " << d_strings.size() << endl;
  }

  if(!d_ptrs.empty()){
    out << " AM d_ptrs " << d_ptrs.size() << endl;
  }
  if(!d_cdbools.empty()){
    out << " AM d_cdbools " << d_cdbools.size() << endl;
  }
  if(!d_cdints.empty()){
    out << " AM d_cdints " << d_cdints.size() << endl;
  }
  if(!d_cdtnodes.empty()){
    out << " AM d_cdtnodes" << d_cdtnodes.size() << endl;
  }
  if(!d_cdnodes.empty()){
    out << " AM d_cdnodes " << d_cdnodes.size() << endl;
  }
  if(!d_bools.empty()){
    out << " AM d_cdstrings " << d_cdstrings.size() << endl;
  }
  if(!d_cdptrs.empty()){
    out << " AM d_cdptrs " << d_cdptrs.size() << endl;
  }
}

void AttributeManager::deleteAllAttributes(NodeValue* nv) {
  d_bools.erase(nv);
  deleteFromTable(d_ints, nv);
  deleteFromTable(d_tnodes, nv);
  deleteFromTable(d_nodes, nv);
  deleteFromTable(d_types, nv);
  deleteFromTable(d_strings, nv);
  deleteFromTable(d_ptrs, nv);

  d_cdbools.erase(nv);
  deleteFromTable(d_cdints, nv);
  deleteFromTable(d_cdtnodes, nv);
  deleteFromTable(d_cdnodes, nv);
  deleteFromTable(d_cdstrings, nv);
  deleteFromTable(d_cdptrs, nv);
}

void AttributeManager::deleteAllAttributes() {
  d_bools.clear();
  deleteAllFromTable(d_ints);
  deleteAllFromTable(d_tnodes);
  deleteAllFromTable(d_nodes);
  deleteAllFromTable(d_types);
  deleteAllFromTable(d_strings);
  deleteAllFromTable(d_ptrs);

  d_cdbools.clear();
  d_cdints.clear();
  d_cdtnodes.clear();
  d_cdnodes.clear();
  d_cdstrings.clear();
  d_cdptrs.clear();
}

void AttributeManager::deleteAttributes(const AttrIdVec& atids){
  typedef std::map<uint64_t, std::vector< uint64_t> > AttrToVecMap;
  AttrToVecMap perTableIds;

  //cout << "here " << endl;
  for(AttrIdVec::const_iterator it = atids.begin(), it_end = atids.end(); it != it_end; ++it){
    const AttributeUniqueId& pair = *(*it);
    //cout << pair.getTableId() << ", " << pair.getWithinTypeId()  << endl;
    std::vector< uint64_t>& inTable = perTableIds[pair.getTableId()];
    inTable.push_back(pair.getWithinTypeId());
  }
  AttrToVecMap::iterator it = perTableIds.begin(), it_end = perTableIds.end();
  for(; it != it_end; ++it){
    Assert(((*it).first) <= LastAttrTable);
    AttrTableId tableId = (AttrTableId) ((*it).first);
    std::vector< uint64_t>& ids = (*it).second;
    std::sort(ids.begin(), ids.end());

    // //cout << "deleting " << endl;
    // cout << tableId << endl;
    // for(unsigned i=0; i < ids.size(); ++i){
    //   cout << ids[i] << ", " ;
    // }
    // cout << endl;

    switch(tableId){
    case AttrTableBool:
#warning "Iterating over AttrHash<bool> tables is unsupported!"
      Unimplemented("delete attributes is unimplemented for bools");
      break;
    case AttrTableUInt64:
      deleteAttributesFromTable(d_ints, ids);
      break;
    case AttrTableTNode:
      deleteAttributesFromTable(d_tnodes, ids);
      break;
    case AttrTableNode:
      deleteAttributesFromTable(d_nodes, ids);
      break;
    case AttrTableTypeNode:
      deleteAttributesFromTable(d_types, ids);
      break;
    case AttrTableString:
      deleteAttributesFromTable(d_strings, ids);
      break;
    case AttrTablePointer:
#warning "Clear  AttributeManager::reconstructTable(AttrHash<T>& table) with Morgan before this goes into trunk!"
      deleteAttributesFromTable(d_ptrs, ids);
      break;

    case AttrTableCDBool:
    case AttrTableCDUInt64:
    case AttrTableCDTNode:
    case AttrTableCDNode:
    case AttrTableCDString:
    case AttrTableCDPointer:
      Unimplemented("CDAttributes cannot be deleted. Contact Tim/Morgan if this behaviour is desired.");
      break;
    case LastAttrTable:
    default:
      Unreachable();
    }
  }
}

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
