/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef SOLVER_HH_
#define SOLVER_HH_

#include <memory>
#include <sstream>
#include <unordered_map>

#include "common.hh"

namespace ConcuBinE {

//==============================================================================
// forward declarations
//==============================================================================

struct Encoder;
class Trace;

//==============================================================================
// Solver
//
// * abstract base class
//==============================================================================

struct Solver
{
  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // get name
  //
  virtual std::string name () const = 0;

  // get version
  //
  virtual std::string version () const = 0;

  // build formula from given encoding
  //
  virtual std::string formula (Encoder & encoder) const;

  // evaluate arbitrary formula
  //
  virtual bool sat (const std::string & formula) = 0;

  // solve given encoding and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder) = 0;

  //----------------------------------------------------------------------------
  // public data members
  //----------------------------------------------------------------------------

  // runtime in seconds
  //
  double time;

  // the solver's output
  //
  std::stringstream stdout;
};

//==============================================================================
// External
//
// * abstract base class for solvers running in a forked process
//==============================================================================

class External : public Solver
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // get command line
  //
  virtual std::vector<std::string> command () const = 0;

  //----------------------------------------------------------------------------
  // public member functions inherited from Solver
  //----------------------------------------------------------------------------

  // evaluate arbitrary formula
  //
  virtual bool sat (const std::string & formula);

  // solve given encoding and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder);

protected: //===================================================================

  //----------------------------------------------------------------------------
  // protected member types
  //----------------------------------------------------------------------------

  // current symbol while parsing
  //
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
  // protected member functions
  //----------------------------------------------------------------------------

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

  //----------------------------------------------------------------------------
  // protected data members
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

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // detect an eventual heap update
  //
  void update_heap (Trace & trace, size_t prev, size_t cur);

  // build trace based on the solver's output
  //
  std::unique_ptr<Trace> trace (const Encoder & encoder);
};

} // namespace ConcuBinE

#endif
