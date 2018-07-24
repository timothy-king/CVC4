#include "cvc4_private.h"

#ifndef __CVC4__MAP_UTIL_H
#define __CVC4__MAP_UTIL_H

#include "base/cvc4_check.h"

namespace CVC4 {

// Returns true if the `map` contains the `key`.
//
// Supports sets as well.
template <class M, class Key>
bool ContainsKey(const M& map, const Key& key) {
  return map.find(key) != map.end();
}

template <typename M>
using MapKeyTypeT = typename M::value_type::first_type;
template <typename M>
using MapMappedTypeT = typename M::value_type::second_type;


// Returns a pointer to the non-const value mapped by `key` if it exists, or
// nullptr otherwise.

template <class M>
const MapMappedTypeT<M>* FindOrNull(const M& map, const MapKeyTypeT<M>& key) {
  auto it = map.find(key);
  if (it == map.end()){
    return nullptr;
  }
  return &((*it).second);
}

template <class M>
MapMappedTypeT<M>* FindOrNull(M& map, const MapKeyTypeT<M>& key) {
  auto it = map.find(key);
  if (it == map.end()){
    return nullptr;
  }
  return &((*it).second);
}

// Returns a const reference to the value mapped by `key` if it exists. Dies
// if the element is not there.
template <class M>
const MapMappedTypeT<M>& FindOrDie(const M& map, const MapKeyTypeT<M>& key) {
  auto it = map.find(key);
  CVC4_CHECK(it != map.end()) << "The map does not contain the key.";
  return (*it).second;
}

}  // namespace CVC4

#endif /* __CVC4__MAP_UTIL_H */
