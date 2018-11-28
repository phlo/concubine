#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <array>
#include <functional>
#include <unordered_map>

#include "common.hh"
#include "thread.hh"

/* forward declarations */
struct Schedule;

/*******************************************************************************
 * Machine
 ******************************************************************************/
struct Machine
{
  /* constructs a new machine with given seed and bound */
  Machine (unsigned long seed = 0, unsigned long bound = 0);

  /*****************************************************************************
   * variables
   ****************************************************************************/

  /* thread scheduling */
  unsigned long                         seed;

  /* bounded execution */
  unsigned long                         bound;

  /* list of active threads */
  ThreadList                            active;

  /* list of all threads */
  ThreadList                            threads;

  /* machine memory */
  std::array<word, word_max>            memory;

  /* number of threads containing calls to a specific sync barrier (id) */
  std::unordered_map<word, ThreadList>  threadsPerSyncID;

  /* number of threads currently waiting for a specific sync barrier (id) */
  std::unordered_map<word, word>        waitingPerSyncID;

  /*****************************************************************************
   * private functions
   ****************************************************************************/

  /* adds all threads to the active queue and sets them running */
  void                                  activateThreads (ThreadList &);

  /* checks if all threads reached the given barrier id and resumes them */
  void                                  checkAndResumeWaiting (word);

  /* run the machine, using the specified scheduler */
  int                                   run (std::function<ThreadPtr(void)>);

  /*****************************************************************************
   * public functions
   ****************************************************************************/

  /* creates a thread using the given program, thread id == number of threads*/
  ThreadID                              createThread (Program &);

  /* runs the machine using a random schedule */
  int                                   simulate (void);

  /* replay the given schedule (schedule must match machine configuration) */
  int                                   replay (Schedule &);
};

#endif
