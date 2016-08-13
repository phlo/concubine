#include "solver.hh"

#include <cstdio>
#include <stdexcept>

#include "shell.hh"

/* Solver::execute (string &) *************************************************/
int Solver::execute (string & formula)
{
  Shell shell;

  stdOut = shell.run(buildCommand(), formula);

  return shell.lastExitCode();
}
