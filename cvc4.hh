#ifndef CVC4_HH_
#define CVC4_HH_

#include "solver.hh"

class CVC4 : public ExternalSolver
{
  virtual std::string build_command ();

  virtual std::string build_formula (Encoder & encoder, std::string & constraints);

  virtual std::optional<Variable> parse_line (std::istringstream &);

public:

  virtual std::string name () const;
};

typedef std::shared_ptr<CVC4> CVC4Ptr;

#endif
