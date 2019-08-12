#ifndef BTORMC_HH
#define BTORMC_HH

#include "boolector.hh"

namespace ConcuBinE {

struct BtorMC : public Boolector
{
  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  const size_t bound;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  BtorMC (size_t);

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  virtual std::string name () const;

  virtual std::string command ();

  virtual Symbol symbol (std::istringstream &);

  virtual Symbol parse (std::istringstream &);
};

} // namespace ConcuBinE

#endif
