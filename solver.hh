#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <memory>
#include <sstream>

using namespace std;

/*******************************************************************************
 * SolverPtr
 ******************************************************************************/
struct Solver
{
  string          stdOut;

  int             execute (string &);

  virtual string  buildCommand (void) = 0;

  virtual bool    sat (string &) = 0;
};


/*******************************************************************************
 * SolverPtr
 ******************************************************************************/
typedef shared_ptr<Solver> SolverPtr;

#endif
