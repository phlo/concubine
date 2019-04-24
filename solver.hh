#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <memory>
#include <sstream>

#include "schedule.hh"

struct Encoder;

struct Solver
{
  /* build formula for the specific solver */
  virtual std::string build_formula (Encoder & encoder, std::string & constraints);

  /* returns the solver's name */
  virtual std::string name () const = 0;

  /* evaluate arbitrary formula */
  virtual bool        sat (std::string & formula) = 0;

  /* run solver and return schedule */
  virtual SchedulePtr solve (Encoder & encoder, std::string & constraints) = 0;

  // TODO: remove - redundant, use build_formula instead
  /* print the complete (formula + specification) to stdout */
  void                print (Encoder & encoder, std::string & constraints);
};

typedef std::shared_ptr<Solver> SolverPtr;

/* Base class for solvers running in a forked process. */
struct ExternalSolver : public Solver
{
  struct Variable
    {
      enum class Type
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

  /* the solver's stdout */
  std::stringstream std_out;

  // TODO: find better name - parse_part?
  /* parse variable metadata (step, thread, pc) */
  // unsigned long parse_suffix (std::istringstream & line, const std::string name);

  /* build command line for the specific solver */
  virtual std::string build_command () = 0;

  /* build schedule based on the specific solver's output */
  SchedulePtr build_schedule (ProgramListPtr programs);

  virtual std::optional<Variable> parse_variable (std::istringstream & line);

  virtual std::optional<Variable> parse_line (std::istringstream & line) = 0;

  virtual bool sat (std::string & formula);

  virtual SchedulePtr solve (Encoder & encoder, std::string & constraints);
};

#endif
