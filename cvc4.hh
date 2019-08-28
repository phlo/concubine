#ifndef CVC4_HH_
#define CVC4_HH_

#include "solver.hh"

namespace ConcuBinE {

//==============================================================================
// CVC4 class
//
// NOTE: seems like CVC4 always assigns uninitialized array elements with zero
//==============================================================================

struct CVC4 : public External
{
  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // return cvc4's name
  //
  virtual std::string name () const;

  // build formula for cvc4
  //
  virtual std::string formula (Encoder & encoder) const;

  // build command line for the specific solver
  //
  virtual std::string command () const;

  // parse variable
  //
  virtual Symbol parse (std::istringstream &);
};

} // namespace ConcuBinE

#endif
