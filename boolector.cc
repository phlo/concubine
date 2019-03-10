#include "boolector.hh"

#include <sstream>

using namespace std;

string Boolector::build_command ()
{
  return "boolector -m";
}

SchedulePtr Boolector::build_schedule ()
{
  // TODO
  if (std_out.empty())
    throw runtime_error("missing model");

  SchedulePtr schedule;

  istringstream model(std_out);

  return schedule;
}
