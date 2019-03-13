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
struct Schedule : public std::deque<ThreadID>
{
  /* default constructor (for testing) */
  Schedule (void);

  /* construct from simulator/solver */
  Schedule (ProgramListPtr, unsigned long, unsigned long);

  /* construct from file */
  Schedule (std::istream &, std::string &);

  /* path to schedule file */
  std::string           path;

  /* bound used == size() */
  unsigned long         bound;

  /* seed used to produce that particular schedule */
  unsigned long         seed;

  /* programs used to generate the schedule */
  ProgramListPtr        programs;

  /* exit code */
  word                  exit;

  /* thread state maps */
  std::unordered_map<
    word,
    std::vector<word>>  accus,
                        mems,
                        pcs;

  /* heap states */
  std::vector<
    std::unordered_map<
      word,
      word>>            heap;
};

/*******************************************************************************
 * SchedulePtr
 ******************************************************************************/
typedef std::shared_ptr<Schedule> SchedulePtr;

#endif
