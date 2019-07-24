#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

namespace ConcuBinE {

class Boolector : public External
{
  virtual std::string build_command ();

protected:

  virtual Symbol parse_line (std::istringstream & line);

public:

  virtual std::string name () const;
};

} // namespace ConcuBinE

#endif
