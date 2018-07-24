/*********************                                                        */
/*! \file cdtrail_hashmap_forward.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is a forward declaration header to declare the
 ** NotUsedTrailHashMap<> template
 **
 ** This is a forward declaration header to declare the NotUsedTrailHashMap<>
 ** template.  It's useful if you want to forward-declare NotUsedTrailHashMap<>
 ** without including the full cdtrail_hash_map.h header, for example, in a
 ** public header context.
 **
 ** For NotUsedTrailHashMap<> in particular, it's difficult to forward-declare it
 ** yourself, because it has a default template argument.
 **/

#include "cvc4_public.h"

#pragma once

#include <functional>

namespace CVC4 {
  namespace context {
    template <class Key, class Data, class HashFcn = std::hash<Key> >
    class NotUsedTrailHashMap;
  }/* CVC4::context namespace */
}/* CVC4 namespace */
