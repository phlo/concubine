#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <string>
#include <memory>

/*******************************************************************************
 * Solver
 ******************************************************************************/
struct Solver
{
  std::string           std_out;

  int                   execute (std::string &);

  virtual std::string   build_command (void) = 0;

  virtual bool          sat (std::string &) = 0;
};


/*******************************************************************************
 * SolverPtr
 ******************************************************************************/
typedef std::shared_ptr<Solver> SolverPtr;

#endif
