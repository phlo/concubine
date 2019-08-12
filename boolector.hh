#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

namespace ConcuBinE {

//==============================================================================
// Boolector class
//==============================================================================

class Boolector : public External
{
private: //---------------------------------------------------------------------

  virtual std::string command ();

protected: //-------------------------------------------------------------------

  virtual Symbol parse (std::istringstream & line);

public: //----------------------------------------------------------------------

  virtual std::string name () const;
};

} // namespace ConcuBinE

#endif
