#include "solver.hh"

#include <iostream>

#include "encoder.hh"
#include "shell.hh"
#include "smtlib.hh"

using namespace std;

bool Solver::sat (string & input)
{
  Shell shell;

  std_out = shell.run(build_command(), input);

  cout << std_out;

  return !std_out.compare(0, 3, "sat");
}

void Solver::print (Encoder & formula, string & constraints)
{
  cout << build_formula(formula, constraints);
}

SchedulePtr Solver::solve (Encoder & formula, string & constraints)
{
  Shell shell;

  string input = build_formula(formula, constraints);

  std_out = shell.run(build_command(), input);

  exit_code = shell.last_exit_code();

  cout << std_out;

  return build_schedule();
}

string SMTLibSolver::build_formula (Encoder & formula, string & constraints)
{
  return
    formula.str() + eol +
    (constraints.empty() ? "" : constraints + eol) +
    smtlib::check_sat() + eol +
    smtlib::exit() + eol;
}
