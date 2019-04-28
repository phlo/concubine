#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

class Boolector : public ExternalSolver
{
  virtual std::string build_command ();

protected:
  virtual std::optional<Variable> parse_line (std::istringstream & line);

public:

  virtual std::string name () const;
};

typedef std::shared_ptr<Boolector> BoolectorPtr;

#endif
