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

  virtual std::string name () const;

  virtual std::string command ();

  virtual std::string formula (Encoder & encoder,
                               const std::string & constraints);

  virtual Symbol parse (std::istringstream &);
};

} // namespace ConcuBinE

#endif
