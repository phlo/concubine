#include "cvc4.hh"

#include "smtlib.hh"

using namespace std;

string CVC4::name () { return "cvc4"; }

string CVC4::build_command ()
{
  return "cvc4 -L smt2 -m --output-lang=cvc4";
}

string CVC4::build_formula (Encoder & formula, string & constraints)
{
  return
    SMTLibSolver::build_formula(formula, constraints) +
    smtlib::get_model();
}

optional<Solver::Variable> CVC4::parse_line (istringstream & line)
{
  // TODO
  (void) line;

  return {};
}
