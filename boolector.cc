#include "boolector.hh"

using namespace std;

string Boolector::build_command ()
{
  return "boolector -m";
}

SchedulePtr Boolector::build_schedule ()
{
  // TODO
  if (!std_out.rdbuf()->in_avail())
    throw runtime_error("missing model");

  SchedulePtr schedule;

  return schedule;
}
