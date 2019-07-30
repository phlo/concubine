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
  // members
  //----------------------------------------------------------------------------

  // solving time in milliseconds
  //
  long time;

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

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

struct External : Solver
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  enum class Symbol
    {
      ignore,
      accu,
      mem,
      sb_adr,
      sb_val,
      sb_full,
      heap,
      stmt,
      thread,
      flush,
      exit_flag,
      exit_code
    };

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // current step
  //
  size_t step;

  // current thread
  //
  word_t thread;

  // current pc
  //
  word_t pc;

  // current address
  //
  word_t address;

  // current value
  //
  word_t value;

  // the solver's stdout
  //
  std::stringstream std_out;

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  virtual bool sat (const std::string & formula);

  virtual Trace::ptr solve (Encoder & encoder, const std::string & constraints);

  // build command line for the specific solver
  //
  virtual std::string build_command () = 0;

  // build trace based on the specific solver's output
  //
  Trace::ptr build_trace (const Program::List::ptr & programs);

  // parse integer attribute of current symbol
  //
  size_t parse_symbol (std::istringstream & line,
                       const std::string & name,
                       char delimiter = '_');

  // parse current variable's symbol
  //
  virtual Symbol parse_symbol (std::istringstream & line);

  // parse variable
  //
  virtual Symbol parse_line (std::istringstream & line) = 0;
};

} // namespace ConcuBinE

#endif
