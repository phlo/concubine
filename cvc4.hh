#ifndef CVC4_HH_
#define CVC4_HH_

#include "solver.hh"

struct CVC4 : public SMTLibSolver
{
  virtual std::string             name (void);

  virtual std::string             build_command (void);

  virtual std::string             build_formula (Encoder &, std::string &);

  virtual std::optional<Variable> parse_line (std::istringstream &);
};

typedef std::shared_ptr<CVC4> CVC4Ptr;

#endif
