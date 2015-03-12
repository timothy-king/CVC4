/*********************                                                        */
/*! \file cdconsequent_tracker.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: None
 ** Minor contributors (to current version): None
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context-dependent list class (only supports append)
 **
 ** Context-dependent list class.  This list only supports appending
 ** to the list; on backtrack, the list is simply shortened.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDCONSEQUENT_TRACKER_H
#define __CVC4__CONTEXT__CDCONSEQUENT_TRACKER_H

#include <stdint.h>
#include <iterator>
#include <memory>
#include "util/cvc4_assert.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdlist_forward.h"


namespace CVC4 {
namespace context {


class ConsequentID {
private:
  uint32_t d_pos;
  static const uint32_t SentinelValue = UINT32_MAX;
  
public:
  static const ConsequentID Sentinel;
  
  ConsequentID(){}
  ConsequentID(uint32_t p) : d_pos(p){}

  inline operator uint32_t() const { return d_pos; }
  inline bool operator==( ConsequentID cid) const { return d_pos == cid.d_pos; }
  inline bool operator!=( ConsequentID cid) const { return d_pos != cid.d_pos; }
  inline bool operator< ( ConsequentID cid) const { return d_pos <  cid.d_pos; }
  inline bool operator<=( ConsequentID cid) const { return d_pos <= cid.d_pos; }
  
  inline bool isSentinel() const{ return d_pos == SentinelValue; }
  
}; /* ConsequentID */

template <class T, class CleanUpT = DefaultCleanUp<T>, class AllocatorT = std::allocator<T> >
class CDConsequentTracker {
public:
  typedef T value_type;
  typedef CleanUpT CleanUp;
  typedef AllocatorT Allocator;

  
private:

  typedef context::CDList< T, CleanUp, Allocator > ConsequentList;
  ConsequentList d_consequents;
  
  struct PositionPair {
  private:
    uint32_t d_antecedentsBegin;
    uint32_t d_antecedentsSize;
  public:
    PositionPair() : d_antecedentsBegin(UINT32_MAX), d_antecedentsSize(0){}
    PositionPair(uint32_t begin, uint32_t size)
    : d_antecedentsBegin(begin), d_antecedentsSize(size)
    {
      Assert( begin <= begin+size );
    }
    inline bool empty() const { return d_antecedentsSize == 0; }
    inline uint32_t size() const { return d_antecedentsSize; }
    inline uint32_t begin(){ return d_antecedentsBegin; }
    inline uint32_t end() const{
      return d_antecedentsBegin + d_antecedentsSize;
    }
    inline uint32_t offset(uint32_t i) const {
      Assert(i < d_antecedentsSize);
      return d_antecedentsBegin + i;
    }
  };
  
  typedef context::CDList< PositionPair > AntecedentPositionList;
  AntecedentPositionList d_antecedentPositions;
  

public:
  

private:
  typedef typename context::CDList<ConsequentID> AntecedentList;
  AntecedentList d_antecedents;

public:
  typedef typename AntecedentList::const_iterator antecedent_iterator;
  
public:
 CDConsequentTracker(Context* context,
		     bool callDestructor = true,
		     const CleanUp& cleanup = CleanUp(),
		     const Allocator& alloc = Allocator())
   : d_consequents(context, callDestructor, cleanup, alloc)
    , d_antecedentPositions(context, false)
    , d_antecedents(context, false)
    {}
  
  CDConsequentTracker& operator=(const CDConsequentTracker& l) CVC4_UNDEFINED;

  ConsequentID track(const T& t){
    Assert ( d_consequents.size() < UINT32_MAX );
    uint32_t pos = (uint32_t)d_consequents.size();
    d_consequents.push_back(t);
    d_antecedentPositions.push_back(PositionPair());
    return ConsequentID(pos);
  }
  
  ConsequentID track(const T& t, ConsequentID a0){
    Assert ( d_consequents.size() < UINT32_MAX );
    uint32_t pos = (uint32_t)d_consequents.size();
    d_consequents.push_back(t);
    
    Assert ( d_antecedents.size() < UINT32_MAX );
    d_antecedentPositions.push_back(PositionPair((uint32_t)d_antecedents.size(), 1));
    d_antecedents.push_back(a0);
    
    return ConsequentID(pos);
  }
  
  ConsequentID track(const T& t, ConsequentID a0, ConsequentID a1){
    Assert ( d_consequents.size() < UINT32_MAX );
    uint32_t pos = (uint32_t)d_consequents.size();
    d_consequents.push_back(t);
    
    Assert ( d_antecedents.size() < UINT32_MAX );
    d_antecedentPositions.push_back(PositionPair((uint32_t)d_antecedents.size(), 2));
    d_antecedents.push_back(a0);
    Assert ( d_antecedents.size() < UINT32_MAX );
    d_antecedents.push_back(a1);
    
    return ConsequentID(pos);
  }
  
  ConsequentID track(const T& t, const std::vector<ConsequentID>& as){
    Assert ( d_consequents.size() < UINT32_MAX );
    uint32_t pos = (uint32_t)d_consequents.size();
    d_consequents.push_back(t);
    
    Assert ( d_antecedents.size() < UINT32_MAX );
    Assert ( as.size() < UINT32_MAX );
    Assert ( d_antecedents.size() + as.size() < UINT32_MAX );
    d_antecedentPositions.push_back(PositionPair((uint32_t)d_antecedents.size(), (uint32_t)as.size()));
    
    typename std::vector<ConsequentID>::const_iterator a_i = as.begin(), a_end = as.end();
    for(; a_i != a_end; ++a_i){
      d_antecedents.push_back(*a_i);
    }
    return ConsequentID(pos);
  }

  inline const T& getValue(const ConsequentID& cid) const{
    Assert(debugInRange(cid));
    return d_consequents[(uint32_t)cid];
  }
  
  inline uint32_t getNumAntecedents(ConsequentID cid) const {
    Assert(debugInRange(cid));
    return d_antecedentPositions[cid].size();
  }

  inline ConsequentID getAntecedent(ConsequentID cid, uint32_t i){
    Assert(debugInRange(cid));
    const PositionPair& pp = d_antecedentPositions[cid];
    Assert(debugInRange(pp));
    return d_antecedents[pp.offset(i)];
  }

  inline bool hasAntecedents(ConsequentID cid) const {
    Assert(debugInRange(cid));
    return !d_antecedentPositions[cid].empty();
  }
  
  inline antecedent_iterator begin_antecedents(ConsequentID cid) const {
    Assert(debugInRange(cid));
    const PositionPair& pp = d_antecedentPositions[cid];
    return d_antecedents.begin() + pp.begin();
  }

  inline antecedent_iterator end_antecedents(ConsequentID cid) const {
    Assert(debugInRange(cid));
    const PositionPair& pp = d_antecedentPositions[cid];
    Assert(debugInRange(pp));
    return d_antecedents.begin() + pp.end();
  }

  inline void push_back_antecedents(ConsequentID cid, std::vector<ConsequentID>& out) const {
    for(antecedent_iterator i = begin(), i_end = end; i != i_end; ++i){
      out.push_back(*i);
    }
  }
  
  class const_iterator{
  private:
    ConsequentID d_it;

    const_iterator(const ConsequentID& cid) : d_it(cid) {}
    friend class CDConsequentTracker<T, CleanUp, Allocator>;

  public:
    typedef std::input_iterator_tag iterator_category;
    typedef ConsequentID value_type;
    typedef std::size_t difference_type;
    typedef const ConsequentID* pointer;
    typedef const ConsequentID& reference;

    const_iterator() : d_it() {}
    
    inline bool operator==(const const_iterator& i) const {
      return d_it == i.d_it;
    }

    inline bool operator!=(const const_iterator& i) const {
      return d_it != i.d_it;
    }
    
    inline const T& operator*() const {
      return d_it;
    }
    
    /** Prefix increment */
    const_iterator& operator++() {
      d_it = ConsequentID( ((uint32_t)d_it) + 1);
      return *this;
    }
  };

  const_iterator begin() const {
    return const_iterator(ConsequentID(0));
  }
  const_iterator end() const {
    return const_iterator(ConsequentID(d_consequents.size()));
  }

 private:
  bool debugInRange(const ConsequentID& cid){
    return ((uint32_t)cid < d_consequents.size());
  }
  bool debugInRange(const PositionPair& pp){
    return pp.begin() <= d_antecedents.size() &&
      pp.end() <= d_antecedents.size();
  }
}; /* class CDConsequentTracker<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* #define __CVC4__CONTEXT__CDCONSEQUENT_TRACKER_H */
