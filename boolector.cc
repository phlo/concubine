#include "boolector.hh"

#include "encoder.hh"
#include "smtlib.hh"

using namespace std;

string Boolector::build_command ()
{
  return "boolector -m";
}

string Boolector::build_formula (Encoder & formula, string & constraints)
{
  return
    formula.str() + eol +
    (constraints.empty() ? "" : constraints + eol) +
    smtlib::check_sat() + eol +
    smtlib::exit() + eol;
}

SchedulePtr Boolector::build_schedule ()
{
  return nullptr; // TODO
}
