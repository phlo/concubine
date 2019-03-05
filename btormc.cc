#include "btormc.hh"

#include "encoder.hh"

using namespace std;

string BtorMC::build_command ()
{
  return "btormc --trace-gen-full";
}

string BtorMC::build_formula (Encoder & formula, string & constraints)
{
  return formula.str() + (constraints.empty() ? "" : constraints + eol);
}

SchedulePtr BtorMC::build_schedule ()
{
  return nullptr; // TODO
}
