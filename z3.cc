#include "z3.hh"

using namespace std;

string Z3::name () { return "z3"; }

string Z3::build_command ()
{
  return "z3 dump_models=true model.v2=true pp.single_line=true -in";
}

optional<Solver::Variable> Z3::parse_line (istringstream & line)
{
  (void) line;

  return {};
}
