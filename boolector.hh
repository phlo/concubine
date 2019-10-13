#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

namespace ConcuBinE {

//==============================================================================
// Boolector class
//==============================================================================

class Boolector : public External
{
  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

private: //---------------------------------------------------------------------

  // build command line for running boolector
  //
  virtual const std::vector<std::string> & command () const;

protected: //-------------------------------------------------------------------

  // parse variable
  //
  virtual Symbol parse (std::istringstream & line);

public: //----------------------------------------------------------------------

  // return boolector's name
  //
  virtual std::string name () const;

  // return boolector's version
  //
  virtual std::string version () const;
};

} // namespace ConcuBinE

#endif
