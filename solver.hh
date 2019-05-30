#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <memory>
#include <sstream>

#include "schedule.hh"

struct Encoder;

struct Solver
{
  bound_t parse_attribute (
                           std::istringstream & line,
                           const std::string name,
                           const char delimiter = '_'
                          );

  /* build formula for the specific solver */
  virtual std::string build_formula (Encoder & encoder, std::string & constraints);

  /* returns the solver's name */
  virtual std::string name () const = 0;

  /* evaluate arbitrary formula */
  virtual bool sat (std::string & formula) = 0;

  /* run solver and return schedule */
  virtual Schedule_ptr solve (Encoder & encoder, std::string & constraints) = 0;
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

      Type    type;
      bound_t step;
      word_t  thread;
      word_t  pc;
      word_t  adr;
      word_t  val;
    };

  /* the solver's stdout */
  std::stringstream std_out;

  /* build command line for the specific solver */
  virtual std::string build_command () = 0;

  /* build schedule based on the specific solver's output */
  Schedule_ptr build_schedule (Program_list_ptr programs);

  virtual std::optional<Variable> parse_variable (std::istringstream & line);

  virtual std::optional<Variable> parse_line (std::istringstream & line) = 0;

  virtual bool sat (std::string & formula);

  virtual Schedule_ptr solve (Encoder & encoder, std::string & constraints);
};

#endif
