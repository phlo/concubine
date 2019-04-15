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

  /* bound */
  unsigned long       bound;

  /* print the complete (formula + specification) to stdout */
  void                print (Encoder &, std::string &);

  /* evaluate arbitrary formula */
  bool                sat (std::string &);

  /* run solver and return schedule */
  SchedulePtr         solve (Encoder &, std::string &);

  /* build schedule based on the specific solver's output */
  SchedulePtr         build_schedule (ProgramListPtr);

  /* returns the solver's name */
  virtual std::string name (void) = 0;

  /* build command line for the specific solver */
  virtual std::string build_command (void) = 0;

  /* build formula for the specific solver */
  virtual std::string build_formula (Encoder &, std::string &) = 0;

  struct Variable
    {
      enum Type
        {
          THREAD,
          EXEC,
          ACCU,
          MEM,
          HEAP,
          EXIT,
          EXIT_CODE
        };

      Type          type;
      unsigned long step;
      word          thread;
      word          pc;
      word          idx;
      word          val;
    };

  word                parse_thread (std::istringstream &);

  word                parse_pc (std::istringstream &);

  virtual std::optional<Variable> parse_line (std::istringstream &) = 0;
  virtual std::optional<Variable> parse_variable (std::istringstream &) = 0;
};

typedef std::shared_ptr<Solver> SolverPtr;

/* base class for solvers using SMT-Lib as input */
struct SMTLibSolver : public Solver
{
  virtual std::string build_command (void) = 0;

  virtual std::string build_formula (Encoder &, std::string &);

  unsigned long parse_step (std::istringstream &);
  virtual std::optional<Variable> parse_variable (std::istringstream &);
};

#endif
