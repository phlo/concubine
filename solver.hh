#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <memory>
#include <sstream>

#include "trace.hh"

namespace ConcuBinE {

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

  size_t parse_attribute (std::istringstream & line,
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

  // run solver and return trace
  //
  virtual Trace::ptr solve (Encoder & encoder,
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

      Type   type;
      size_t step;
      word_t thread;
      word_t pc;
      word_t adr;
      word_t val;
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

  // build trace based on the specific solver's output
  //
  Trace::ptr build_trace (const Program::List::ptr & programs);

  virtual std::optional<Variable> parse_variable (std::istringstream & line);

  virtual std::optional<Variable> parse_line (std::istringstream & line) = 0;

  virtual bool sat (const std::string & formula);

  virtual Trace::ptr solve (Encoder & encoder, const std::string & constraints);
};

} // namespace ConcuBinE

#endif
