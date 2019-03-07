#include "boolector.hh"

using namespace std;

string Boolector::build_command ()
{
  return "boolector -m";
}

SchedulePtr Boolector::build_schedule ()
{
  return nullptr; // TODO
}
