#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <string>
#include <memory>

/*******************************************************************************
 * Solver
 ******************************************************************************/
struct Solver
{
  std::string           stdOut;

  int                   execute (std::string &);

  virtual std::string   buildCommand (void) = 0;

  virtual bool          sat (std::string &) = 0;
};


/*******************************************************************************
 * SolverPtr
 ******************************************************************************/
typedef std::shared_ptr<Solver> SolverPtr;

#endif
