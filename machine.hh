#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <array>
#include <deque>
#include <vector>
#include <random>
#include <unordered_map>

#include <cassert>

#include "common.hh"
#include "thread.hh"

using namespace std;

/*******************************************************************************
 * Machine
 ******************************************************************************/
class Machine
{
  friend struct Thread;

  // machine memory
  array<word, numeric_limits<word>::max() + 1>  memory;

  // threads
  deque<ThreadPtr>                              threads;

  // active threads
  deque<ThreadPtr>                              active;

  // lists of threads containing calls to a specific sync barrier (id)
  unordered_map<word, deque<ThreadPtr>>         threadsPerSyncID;

  // lists of threads currently waiting for a specific sync barrier (id)
  unordered_map<word, deque<ThreadPtr>>         waitingPerSyncID;

  // bounded execution
  unsigned long                                 bound;

  // thread scheduling
  unsigned long                                 seed;
  mt19937                                       randomGenerator;

  // adds all threads to the active queue and sets them running
  void  activateThreads (deque<ThreadPtr> &);

public:
  Machine (unsigned long seed, unsigned long bound);

  unsigned int createThread (Program &);

  int run (void);
};
#endif
