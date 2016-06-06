#include "schedule.hh"

/* constructor ****************************************************************/
Schedule::Schedule (string & p) : path(p), seed()
{
  Parser<Schedule> parser(p);
  parser.parse(this);
}

/* Schedule::getPath (void) ***************************************************/
string & Schedule::getPath () { return path; }

/* Schedule::getSeed (void) ***************************************************/
unsigned long Schedule::getSeed () { return seed; }

/* Schedule::getPrograms (void) ***********************************************/
deque<ProgramPtr> & Schedule::getPrograms () { return programs; }

/* Schedule::add (ThreadID) ***************************************************/
void Schedule::add (ThreadID tid) { push_back(tid); }

/* Schedule::add (ProgramPtr) *************************************************/
void Schedule::add (ThreadID tid, ProgramPtr program)
{
  programs.insert(
      programs.begin() + static_cast<difference_type>(tid),
      program
  );
}
