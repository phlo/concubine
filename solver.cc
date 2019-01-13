#include "solver.hh"

#include <iostream>

#include "shell.hh"

using namespace std;

/* Solver::execute (string &) *************************************************/
int Solver::execute (string & formula)
{
  Shell shell;

  std_out = shell.run(build_command(), formula);

  cout << std_out;

  return shell.last_exit_code();
}
