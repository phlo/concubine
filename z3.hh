#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

#include <z3++.h>

namespace ConcuBinE {

//==============================================================================
// Z3 class
//==============================================================================

struct Z3 : public Solver
{
  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  virtual std::string name () const;

  virtual bool sat (const std::string & formula);

  virtual Trace::ptr solve (Encoder & encoder,
                            const std::string & constraints = "");
};

} // namespace ConcuBinE

#endif
