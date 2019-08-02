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

  virtual std::string build_command ();

  virtual std::string build_formula (Encoder & encoder,
                                     const std::string & constraints);

  virtual Symbol parse_line (std::istringstream &);
};

} // namespace ConcuBinE

#endif
