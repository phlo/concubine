#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

#include <z3++.h>

namespace ConcuBinE {

//==============================================================================
// Z3
//==============================================================================

struct Z3 : public Solver
{
  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // return z3's name
  //
  virtual std::string name () const;

  // evaluate arbitrary formula
  //
  virtual bool sat (const std::string & formula);

  // run z3 and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder);
};

} // namespace ConcuBinE

#endif
