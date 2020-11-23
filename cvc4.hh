#ifndef CVC4_HH_
#define CVC4_HH_

#include "solver.hh"

namespace ConcuBinE {

//==============================================================================
// CVC4
//
// NOTE: seems like CVC4 always assigns uninitialized array elements with zero
//==============================================================================

class CVC4 : public External
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public member functions inherited from Solver
  //----------------------------------------------------------------------------

  // get name
  //
  virtual std::string name () const;

  // get version
  //
  virtual std::string version () const;

  // build formula from given encoding
  //
  virtual std::string formula (Encoder & encoder) const;

  //----------------------------------------------------------------------------
  // public member functions inherited from External
  //----------------------------------------------------------------------------

  // get command line
  //
  virtual std::vector<std::string> command () const;

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member functions inherited from External
  //----------------------------------------------------------------------------

  // parse variable
  //
  virtual Symbol parse (std::istringstream &);
};

} // namespace ConcuBinE

#endif
