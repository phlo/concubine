#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <memory>
#include <sstream>

#include "schedule.hh"

//==============================================================================
// forward declarations
//==============================================================================

struct Encoder;

//==============================================================================
// Solver base class
//==============================================================================

struct Solver
{
  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  bound_t parse_attribute (std::istringstream & line,
                           const std::string & name,
                           char delimiter = '_');

  // build formula for the specific solver
  //
  virtual std::string build_formula (Encoder & encoder,
                                     const std::string & constraints);

  // returns the solver's name
  //
  virtual std::string name () const = 0;

  // evaluate arbitrary formula
  //
  virtual bool sat (const std::string & formula) = 0;

  // run solver and return schedule
  //
  virtual Schedule::ptr solve (Encoder & encoder,
                               const std::string & constraints) = 0;
};

//==============================================================================
// External base class
//
// Base class for solvers running in a forked process.
//==============================================================================

struct External : public Solver
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

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

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // the solver's stdout
  //
  std::stringstream std_out;

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // build command line for the specific solver
  //
  virtual std::string build_command () = 0;

  // build schedule based on the specific solver's output
  //
  Schedule::ptr build_schedule (const Program::List::ptr & programs);

  virtual std::optional<Variable> parse_variable (std::istringstream & line);

  virtual std::optional<Variable> parse_line (std::istringstream & line) = 0;

  virtual bool sat (const std::string & formula);

  virtual Schedule::ptr solve (Encoder & encoder,
                               const std::string & constraints);
};

#endif
