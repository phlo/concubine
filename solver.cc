#include "solver.hh"

#include "shell.hh"

using namespace std;

/* Solver::execute (string &) *************************************************/
int Solver::execute (string & formula)
{
  Shell shell;

  stdOut = shell.run(buildCommand(), formula);

  return shell.lastExitCode();
}
