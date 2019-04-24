#include "cvc4.hh"

#include "smtlib.hh"

using namespace std;

string CVC4::name () const { return "cvc4"; }

string CVC4::build_command ()
{
  return "cvc4 -L smt2 -m --output-lang=cvc4";
}

string CVC4::build_formula (Encoder & formula, string & constraints)
{
  return
    Solver::build_formula(formula, constraints) +
    smtlib::check_sat() + eol +
    smtlib::get_model();
}

optional<CVC4::Variable> CVC4::parse_line (istringstream & line)
{
  // TODO
  (void) line;

  return {};
}
