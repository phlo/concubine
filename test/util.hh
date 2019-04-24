#ifndef UTIL_HH_
#define UTIL_HH_

#include <chrono>
#include <functional>

template<typename Duration>
long time (std::function<void()> fun)
{
  using namespace std;
  using namespace std::chrono;

  high_resolution_clock::time_point start = high_resolution_clock::now();
  fun();
  high_resolution_clock::time_point end = high_resolution_clock::now();

  return duration_cast<Duration>(end - start).count();
}

#endif
