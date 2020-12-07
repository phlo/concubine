/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef RUNTIME_HH_
#define RUNTIME_HH_

#include <sys/time.h>
#include <sys/resource.h>

namespace ConcuBinE::runtime {

//==============================================================================
// functions
//==============================================================================

// measure runtime of a given function in seconds using getrusage (user time)
//
template <class Functor>
inline double measure (const Functor & fun)
{
  rusage self, children;
  timeval start, end, elapsed;

  getrusage(RUSAGE_SELF, &self);
  getrusage(RUSAGE_CHILDREN, &children);

  timeradd(&self.ru_utime, &children.ru_utime, &start);

  fun();

  getrusage(RUSAGE_SELF, &self);
  getrusage(RUSAGE_CHILDREN, &children);

  timeradd(&self.ru_utime, &children.ru_utime, &end);

  timersub(&end, &start, &elapsed);

  return elapsed.tv_sec + static_cast<double>(elapsed.tv_usec) / 1000000;
}

} // namespace ConcuBinE::runtime

#endif
