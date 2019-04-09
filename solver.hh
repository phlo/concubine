#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <memory>
#include <sstream>

#include "schedule.hh"

struct Encoder;

struct Solver
{
  /* the solver's stdout */
  std::stringstream   std_out;

  /* the solver's exit code */
  int                 exit_code;

  /* evaluate arbitrary formula */
  bool                sat (std::string &);

  /* print the complete (formula + specification) to stdout */
  void                print (Encoder &, std::string &);

  /* run solver and return schedule */
  SchedulePtr         solve (Encoder &, std::string &);

  /* build command line for the specific solver */
  virtual std::string build_command (void) = 0;

  /* build formula for the specific solver */
  virtual std::string build_formula (Encoder &, std::string &) = 0;

  /* build schedule based on the specific solver's output */
  virtual SchedulePtr build_schedule (void) = 0;
};

typedef std::shared_ptr<Solver> SolverPtr;

/* base class for solvers using SMT-Lib as input */
struct SMTLibSolver : public Solver
{
  virtual std::string build_command (void) = 0;

  virtual std::string build_formula (Encoder &, std::string &);

  virtual SchedulePtr build_schedule (void) = 0;
};

#endif
