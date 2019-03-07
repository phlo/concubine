#include "z3.hh"

using namespace std;

string Z3::build_command ()
{
  return "z3 dump_models=true model.v2=true -in";
}

SchedulePtr Z3::build_schedule ()
{
  return nullptr; // TODO
}
