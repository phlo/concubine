#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

struct Boolector : public SMTLibSolver
{
  virtual std::string             name (void);

  virtual std::string             build_command (void);

  virtual std::optional<Variable> parse_line (std::istringstream &);
};

typedef std::shared_ptr<Boolector> BoolectorPtr;

#endif
