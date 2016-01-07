/*********************                                                        */
/*! \file resource_manager.h
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief Manages and updates various resource and time limits
**
** Manages and updates various resource and time limits.
**/

#include "cvc4_public.h"

#ifndef __CVC4__RESOURCE_MANAGER_H
#define __CVC4__RESOURCE_MANAGER_H

#include <cstddef>
#include <sys/time.h>

#include "base/exception.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {

/**
 * A helper class to keep track of a time budget and signal
 * the PropEngine when the budget expires.
 */
class CVC4_PUBLIC Timer {

  uint64_t d_ms;
  timeval d_wall_limit;
  clock_t d_cpu_start_time;
  clock_t d_cpu_limit;

  bool d_wall_time;

  /** Return the milliseconds elapsed since last set() cpu time. */
  uint64_t elapsedCPU() const;
  /** Return the milliseconds elapsed since last set() wall time. */
  uint64_t elapsedWall() const;

public:

  /** Construct a Timer. */
  Timer()
    : d_ms(0)
    , d_cpu_start_time(0)
    , d_cpu_limit(0)
    , d_wall_time(true)
  {}

  /** Is the timer currently active? */
  bool on() const {
    return d_ms != 0;
  }

  /** Set a millisecond timer (0==off). */
  void set(uint64_t millis, bool wall_time = true);
  /** Return the milliseconds elapsed since last set() wall/cpu time
   depending on d_wall_time*/
  uint64_t elapsed() const;
  bool expired() const;

};/* class Timer */


/**
 * ResourceOutListener is a callback for ResourceManager
 * upon exhausting some resource.
 *
 * This is assumed to call effectly static code with the memory
 * owned by ResourceManager.
 */
class CVC4_PUBLIC ResourceOutListener {
public:
  virtual ~ResourceOutListener(){}

  /** notify() is called on this upon running out of resources. */
  virtual void notifyHard() = 0;

  /** notifySoft() is called on this upon running out of resources. */
  virtual void notifySoft() = 0;

};/* class ResourceOutListener */

class CVC4_PUBLIC ResourceManager {

  Timer d_cumulativeTimer;
  Timer d_perCallTimer;

  /** A user-imposed cumulative time budget, in milliseconds. 0 = no limit. */
  uint64_t d_timeBudgetCumulative;
  /** A user-imposed per-call time budget, in milliseconds. 0 = no limit. */
  uint64_t d_timeBudgetPerCall;
  /** A user-imposed cumulative resource budget. 0 = no limit. */
  uint64_t d_resourceBudgetCumulative;
  /** A user-imposed per-call resource budget. 0 = no limit. */
  uint64_t d_resourceBudgetPerCall;

  /** The number of milliseconds used. */
  uint64_t d_cumulativeTimeUsed;
  /** The amount of resource used. */
  uint64_t d_cumulativeResourceUsed;

  /** The ammount of resource used during this call. */
  uint64_t d_thisCallResourceUsed;

  /**
   * The ammount of resource budget for this call (min between per call
   * budget and left-over cumulative budget.
   */
  uint64_t d_thisCallTimeBudget;
  uint64_t d_thisCallResourceBudget;

  bool d_isHardLimit;
  bool d_on;
  bool d_cpuTime;
  uint64_t d_spendResourceCalls;

  /** Counter indicating how often to check resource manager in loops */
  static const uint64_t s_resourceCount;


  /**
   * This is the listener for the manager.
   * ResourceManager does not own this memory.
   * This is installed and uninstalled.
   * While installed, it is assumed to have the same lifetime as
   * the manager.
   */
  ResourceOutListener* d_listener;

  ResourceManager(const ResourceManager&) CVC4_UNDEFINED;
  ResourceManager& operator=(const ResourceManager&) CVC4_UNDEFINED;

public:

  ResourceManager();
  ~ResourceManager();

  bool limitOn() const { return cumulativeLimitOn() || perCallLimitOn(); }
  bool cumulativeLimitOn() const;
  bool perCallLimitOn() const;

  bool outOfResources() const;
  bool outOfTime() const;
  bool out() const { return d_on && (outOfResources() || outOfTime()); }

  uint64_t getResourceUsage() const;
  uint64_t getTimeUsage() const;
  uint64_t getResourceRemaining() const;
  uint64_t getTimeRemaining() const;

  uint64_t getResourceBudgetForThisCall() {
    return d_thisCallResourceBudget;
  }

  void spendResource(unsigned ammount) throw(UnsafeInterruptException);

  void setHardLimit(bool value);
  void setResourceLimit(uint64_t units, bool cumulative = false);
  void setTimeLimit(uint64_t millis, bool cumulative = false);
  void useCPUTime(bool cpu);

  void enable(bool on);

  /**
   * Resets perCall limits to mark the start of a new call,
   * updates budget for current call and starts the timer
   */
  void beginCall();

  /**
   * Marks the end of a SmtEngine check call, stops the per
   * call timer, updates cumulative time used.
   */
  void endCall();


  /**
   * This installs a new listener into the ResourceManager.
   *
   * This takes over the memory for listener.
   * It is assumed that listener can be deleted.
   * This removes the previously installed listener.
   * NOTE: You may wish to consult SmtResourceOutListener
   * to understand the lifetime of this object.
   */
  void installListener(ResourceOutListener* listener);

  /**
   * Removes an installed listener.
   * @precondition: hasListener()
   * @postcondition: not hasListener()
   */
  void uninstallListener();

  /** Returns true if the current listener is non-NULL. */
  bool hasListener() const;

  static uint64_t getFrequencyCount() { return s_resourceCount; }
};/* class ResourceManager */

}/* CVC4 namespace */

#endif /* __CVC4__RESOURCE_MANAGER_H */
