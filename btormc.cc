#include "btormc.hh"

#include "encoder.hh"

using namespace std;

BtorMC::BtorMC(unsigned long b) : bound(b) {}

string BtorMC::name () const { return "btormc"; }

string BtorMC::build_command ()
{
  return "btormc --trace-gen-full -kmax " + to_string(bound);
}

string BtorMC::build_formula (Encoder & formula, string & constraints)
{
  return formula.str() + (constraints.empty() ? "" : constraints + eol);
}

optional<BtorMC::Variable> BtorMC::parse_line (istringstream & line)
{
  (void) line;

  return {};
}

optional<BtorMC::Variable> BtorMC::parse_variable (istringstream & line)
{
  // TODO
  (void) line;

  return {};
}
