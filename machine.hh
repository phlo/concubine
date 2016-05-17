#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <array>
#include <deque>
#include <vector>
#include <random>

#include <cassert>

#include "thread.hh"

using namespace std;

/* static member won't compile - not a constant expression */
#define REGISTER_SIZE 16
#define MEMORY_SIZE 1 << REGISTER_SIZE

/*******************************************************************************
 * Machine
 ******************************************************************************/
class Machine
{
  friend struct Thread;

  // machine memory
  array<short, MEMORY_SIZE>   memory;

  // threads
  deque<ThreadPtr>            threads;

  // active threads
  deque<ThreadPtr>            active;

  // maps sync barrier IDs to the lists of threads containing them
  // ... or
  // lists of threads containing a specific sync barrier (id)
  unordered_map<short, deque<ThreadPtr>>  threadsPerSyncID;

  // lists of threads waiting for a specific sync barrier (id)
  unordered_map<short, deque<ThreadPtr>>  waitingPerSyncID;

  // bounded execution
  unsigned long               bound;

  // thread scheduling
  unsigned int                seed;
  mt19937                     randomGenerator;

  // adds all threads to the active queue and sets them running
  void activateThreads (deque<ThreadPtr> &);

public:
  Machine (unsigned int seed, unsigned long bound);

  unsigned int createThread (Program &);

  int run (void);
};
#endif
