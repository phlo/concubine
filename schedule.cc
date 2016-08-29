#include "schedule.hh"

#include "parser.hh"

using namespace std;

/* constructors ***************************************************************/
Schedule::Schedule () {}

Schedule::Schedule (string p) : path(p), seed()
{
  if (p.empty())
    throw runtime_error("no schedule given");

  Parser<Schedule> parser(p);
  parser.parse(this);
}

/* Schedule::add (ThreadID) ***************************************************/
void Schedule::add (ThreadID tid) { push_back(tid); }

/* Schedule::add (ProgramPtr) *************************************************/
void Schedule::add (ThreadID tid, ProgramPtr program)
{
  if (programs.size() < tid + 1)
    programs.resize(tid + 1);

  programs[tid] = program;
}
