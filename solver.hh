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

  // returns the solver's name
  //
  virtual std::string name () const = 0;

  // build formula for the specific solver
  //
  virtual std::string formula (Encoder & encoder) const;

  // evaluate arbitrary formula
  //
  virtual bool sat (const std::string & formula) = 0;

  // run solver and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder) = 0;
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

  // current value
  //
  word_t value;

  // current heap state (might contain spurious elements)
  //
  std::unordered_map<word_t, word_t> heap;

  // the solver's stdout
  //
  std::stringstream std_out;

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // build command line for running the specific solver
  //
  virtual std::string command () const = 0;

  // parse integer attribute of current symbol
  //
  size_t attribute (std::istringstream & line,
                    const std::string & name,
                    char delimiter = '_');

  // parse current variable's symbol
  //
  virtual Symbol symbol (std::istringstream & line);

  // parse variable
  //
  virtual Symbol parse (std::istringstream & line) = 0;

  // detect an eventual heap update
  //
  void update_heap (Trace & trace, size_t prev, size_t cur);

  // build trace based on the specific solver's output
  //
  std::unique_ptr<Trace> trace (const Encoder & encoder);

  // evaluate arbitrary formula
  //
  virtual bool sat (const std::string & formula);

  // run solver and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder);
};

} // namespace ConcuBinE

#endif
