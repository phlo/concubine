#ifndef SCHEDULE_HH_
#define SCHEDULE_HH_

#include <string>

#include "program.hh"
#include "thread.hh"

/*******************************************************************************
 * Schedule
 ******************************************************************************/
struct Schedule : public std::deque<ThreadID>
{
  /* default constructor (for testing) */
  Schedule (void);

  /* construct from file */
  Schedule (std::istream &, std::string &);

  /* path to schedule file */
  std::string           path;

  /* seed used to produce that particular schedule */
  unsigned long         seed;

  /* programs used to generate the schedule */
  ProgramList           programs;

  /* append a thread id to be scheduled next */
  void                  add (ThreadID);

  /* add a program */
  void                  add (ThreadID, ProgramPtr);
};

/*******************************************************************************
 * SchedulePtr
 ******************************************************************************/
typedef std::shared_ptr<Schedule> SchedulePtr;

#endif
