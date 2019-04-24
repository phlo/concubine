#ifndef BTORMC_HH
#define BTORMC_HH

#include "solver.hh"

struct BtorMC : public ExternalSolver
{
  BtorMC (unsigned long);

  const unsigned long             bound;

  virtual std::string             build_command (void);

  virtual std::string             build_formula (Encoder &, std::string &);

  virtual std::optional<Variable> parse_line (std::istringstream &);

  virtual std::optional<Variable> parse_variable (std::istringstream &);

  virtual std::string             name (void);
};

typedef std::shared_ptr<BtorMC> BtorMCPtr;

#endif
