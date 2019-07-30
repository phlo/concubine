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

  virtual std::string build_formula (Encoder &, const std::string &);

  virtual std::string build_command ();

  using Boolector::parse_symbol;

  virtual Symbol parse_symbol (std::istringstream &);

  virtual Symbol parse_line (std::istringstream &);
};

} // namespace ConcuBinE

#endif
