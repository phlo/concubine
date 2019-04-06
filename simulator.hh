#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <array>
#include <functional>
#include <unordered_map>

#include "common.hh"
#include "thread.hh"
#include "schedule.hh"

/*******************************************************************************
 * Simulator
 ******************************************************************************/
struct Simulator
{
  /* default constructor (testing only) */
  Simulator (void);

  /* constructs a new simulator for simulation */
  Simulator (ProgramListPtr);

  /*****************************************************************************
   * variables
   ****************************************************************************/

  /* list of programs */
  ProgramListPtr                        programs;

  /* bounded execution */
  unsigned long                         bound;

  /* seed used for thread scheduling */
  unsigned long                         seed;

  /* list of active threads */
  ThreadList                            active;

  /* list of all threads */
  ThreadList                            threads;

  /* main memory */
  std::unordered_map<word, word>        heap;

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
  SchedulePtr                           run (std::function<ThreadPtr(void)>);

  /* creates a thread using the given program, thread id == number of threads*/
  ThreadID                              create_thread (Program &);

  /*****************************************************************************
   * public functions
   ****************************************************************************/

  /* runs the simulator using a random schedule */
  SchedulePtr                           simulate (
                                                  unsigned long bound = 0,
                                                  unsigned long seed = 0
                                                 );

  /* replay the given schedule (schedule must match simulator configuration) */
  SchedulePtr                           replay (
                                                Schedule &,
                                                unsigned long bound = 0
                                               );
};

/*******************************************************************************
 * SimulatorPtr
 ******************************************************************************/
typedef std::shared_ptr<Simulator> SimulatorPtr;

#endif
