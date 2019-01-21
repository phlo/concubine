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
 * Simulator
 ******************************************************************************/
struct Simulator
{
  /* constructs a new simulator with given seed and bound */
  Simulator (unsigned long seed = 0, unsigned long bound = 0);

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

  /* main memory (heap) */
  std::array<word, word_max>            memory;

  /* number of threads containing calls to a specific sync barrier (id) */
  std::unordered_map<word, ThreadList>  threads_per_sync_id;

  /* number of threads currently waiting for a specific sync barrier (id) */
  std::unordered_map<word, word>        waiting_per_sync_id;

  /*****************************************************************************
   * private functions
   ****************************************************************************/

  /* adds all threads to the active queue and sets them running */
  void                                  activate_threads (ThreadList &);

  /* checks if all threads reached the given barrier id and resumes them */
  void                                  check_and_resume_waiting (word);

  /* run the simulator, using the specified scheduler */
  int                                   run (std::function<ThreadPtr(void)>);

  /*****************************************************************************
   * public functions
   ****************************************************************************/

  /* creates a thread using the given program, thread id == number of threads*/
  ThreadID                              create_thread (Program &);

  /* runs the simulator using a random schedule */
  int                                   simulate (void);

  /* replay the given schedule (schedule must match simulator configuration) */
  int                                   replay (Schedule &);
};

#endif
