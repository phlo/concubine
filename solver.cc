#include "solver.hh"

#include "shell.hh"

using namespace std;

/* Solver::execute (string &) *************************************************/
int Solver::execute (string & formula)
{
  Shell shell;

  std_out = shell.run(build_command(), formula);

  return shell.last_exit_code();
}
