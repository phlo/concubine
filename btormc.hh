#ifndef BTORMC_HH
#define BTORMC_HH

#include "boolector.hh"

namespace ConcuBinE {

struct BtorMC : Boolector
{
  BtorMC (size_t);

  const size_t bound;

  virtual std::string build_command ();

  virtual std::string build_formula (Encoder &, const std::string &);

  virtual Symbol parse_line (std::istringstream &);

  using Boolector::parse_symbol;

  virtual Symbol parse_symbol (std::istringstream &);

  virtual std::string name () const;
};

} // namespace ConcuBinE

#endif
