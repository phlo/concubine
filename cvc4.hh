#ifndef CVC4_HH_
#define CVC4_HH_

#include "solver.hh"

class CVC4 : public External
{
private:

  virtual std::string build_command ();

  virtual std::string build_formula (Encoder & encoder,
                                     const std::string & constraints);

  virtual std::optional<Variable> parse_line (std::istringstream &);

public:

  virtual std::string name () const;
};

#endif
