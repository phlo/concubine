#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

namespace ConcuBinE {

//==============================================================================
// Boolector
//==============================================================================

class Boolector : public External
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

  //----------------------------------------------------------------------------
  // public member functions inherited from External
  //----------------------------------------------------------------------------

  // get command line
  //
  virtual const std::vector<std::string> & command () const;

protected: //===================================================================

  //----------------------------------------------------------------------------
  // protected member functions inherited from External
  //----------------------------------------------------------------------------

  // parse variable
  //
  virtual Symbol parse (std::istringstream & line);
};

} // namespace ConcuBinE

#endif
