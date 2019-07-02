#ifndef BTORMC_HH
#define BTORMC_HH

#include "boolector.hh"

struct BtorMC : public Boolector
{
  BtorMC (bound_t);

  const bound_t bound;

  virtual std::string build_command ();

  virtual std::string build_formula (Encoder &, const std::string &);

  virtual std::optional<Variable> parse_line (std::istringstream &);

  virtual std::optional<Variable> parse_variable (std::istringstream &);

  virtual std::string name () const;
};

#endif
