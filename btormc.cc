#include "btormc.hh"

#include "encoder.hh"

using namespace std;

BtorMC::BtorMC(unsigned long b) : bound(b) {}

string BtorMC::build_command ()
{
  return "btormc --trace-gen-full -kmax " + to_string(bound);
}

string BtorMC::build_formula (Encoder & formula, string & constraints)
{
  return formula.str() + (constraints.empty() ? "" : constraints + eol);
}

SchedulePtr BtorMC::build_schedule ()
{
  return nullptr; // TODO
}
