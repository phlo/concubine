#ifndef RUNTIME_HH_
#define RUNTIME_HH_

#include <chrono>

namespace ConcuBinE::runtime {

//==============================================================================
// functions
//==============================================================================

// measure runtime of a given function
//
template <class Functor, class Duration = std::chrono::milliseconds>
inline long measure (const Functor & fun)
{
  const auto begin = std::chrono::high_resolution_clock::now();
  fun();
  const auto end = std::chrono::high_resolution_clock::now();
  return std::chrono::duration_cast<Duration>(end - begin).count();
}

} // namespace ConcuBinE::runtime

#endif
