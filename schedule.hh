#ifndef SCHEDULE_HH_
#define SCHEDULE_HH_

#include <deque>
#include <unordered_set>

#include "thread.hh"
#include "program.hh"

/*******************************************************************************
 * Schedule
 ******************************************************************************/
class Schedule : public deque<ThreadID>
{
  /* be friends with the Parser - for a minimal public interface */
  friend class Parser<Schedule>;

  /* path to schedule file */
  string                path;

  /* seed used to produce that particular schedule */
  unsigned long         seed;

  /* programs used to generate the schedule */
  deque<ProgramPtr>     programs;

  /* append a thread id to be scheduled next */
  void                  add (ThreadID);

  /* add a program */
  void                  add (ThreadID, ProgramPtr);

public:
  Schedule (string &);

  /* sets the used seed */
  unsigned long         getSeed (void);

  /* path to schedule file */
  string &              getPath (void);

  /* programs used */
  deque<ProgramPtr> &   getPrograms (void);
};
#endif
