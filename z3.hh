#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

struct Z3 : public SMTLibSolver
{
  virtual std::string             name (void);

  virtual std::string             build_command (void);

  virtual std::optional<Variable> parse_line (std::istringstream &);
};

typedef std::shared_ptr<Z3> Z3Ptr;

#endif
