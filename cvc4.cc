#include "cvc4.hh"

using namespace std;

string CVC4::build_command ()
{
  return "cvc4 -L smt2 -m --output-lang=cvc4";
}

SchedulePtr CVC4::build_schedule ()
{
  return nullptr; // TODO
}
