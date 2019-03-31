#ifndef SCHEDULE_HH_
#define SCHEDULE_HH_

#include <string>
#include <unordered_map>
#include <vector>

#include "program.hh"
#include "thread.hh"

/*******************************************************************************
 * Schedule
 ******************************************************************************/
struct Schedule : public std::vector<word>
{
  /* default constructor (for testing) */
  Schedule (void);

  /* construct from simulator/solver */
  Schedule (ProgramListPtr);

  /* construct from file */
  Schedule (std::istream &, std::string &);

  /* path to schedule file */
  std::string           path;

  /* bound used == size() */
  unsigned long         bound;

  /* programs used to generate the schedule */
  ProgramListPtr        programs;

  /* exit code */
  word                  exit;

  /* thread states */
  std::vector<
    std::vector<
      std::pair<
        unsigned long,
        word>>>         pc_updates,
                        accu_updates,
                        mem_updates;

  /* heap state updates (idx -> [(step, val), ...]) */
  std::unordered_map<
    word,
    std::vector<
      std::pair<
        unsigned long,
        word>>>         heap_updates;

  /* initialize thread state update lists */
  void                  init_state_update_lists (void);

  /* append thread state update */
  void                  push_back (
                                   const unsigned long step,
                                   const unsigned long tid,
                                   const word pc,
                                   const word accu,
                                   const word mem
                                  );

  /* append heap state update */
  void                  push_back (
                                   const unsigned long step,
                                   const word idx,
                                   const word val
                                  );

  /* add thread state */
  // void                  add (
                             // const unsigned long tid,
                             // const word pc,
                             // const word accu,
                             // const word mem
                            // );

  /* add heap state */
  // void                  add (const std::unordered_map<word, word> & heap);

  /* print schedule */
  std::string           print (void);
};

/*******************************************************************************
 * SchedulePtr
 ******************************************************************************/
typedef std::shared_ptr<Schedule> SchedulePtr;

#endif
