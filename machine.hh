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
#include "schedule.hh"

using namespace std;

/* forward declarations */
struct Scheduler;

/*******************************************************************************
 * Machine
 ******************************************************************************/
class Machine
{
  friend struct Thread;
  friend class  RandomScheduler;
  friend class  PredefinedScheduler;

  /* thread scheduling */
  unsigned long                                 seed;

  /* bounded execution */
  unsigned long                                 bound;

  /* list of active threads */
  deque<ThreadPtr>                              active;

  /* list of all threads */
  deque<ThreadPtr>                              threads;

  /* machine memory */
  array<word, numeric_limits<word>::max() + 1>  memory;

  /* lists of threads containing calls to a specific sync barrier (id) */
  unordered_map<word, deque<ThreadPtr>>         threadsPerSyncID;

  /* lists of threads currently waiting for a specific sync barrier (id) */
  unordered_map<word, deque<ThreadPtr>>         waitingPerSyncID;

  /* add all threads to the active queue and sets them running */
  void  activateThreads (deque<ThreadPtr> &);

  /* run the machine, using the specified scheduler */
  int   run (Scheduler *);

public:
  Machine (unsigned long seed, unsigned long bound);

  /* creates a thread using the given program, thread id == number of threads*/
  ThreadID  createThread (Program &);

  /* runs the machine using a random schedule */
  int       simulate (void);

  /* replay the given schedule (schedule must match machine configuration) */
  int       replay (Schedule &);
};
#endif
