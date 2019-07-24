#ifndef CVC4_HH_
#define CVC4_HH_

#include "solver.hh"

namespace ConcuBinE {

class CVC4 : public External
{
private:

  virtual std::string build_command ();

  virtual std::string build_formula (Encoder & encoder,
                                     const std::string & constraints);

  virtual Symbol parse_line (std::istringstream &);

public:

  virtual std::string name () const;
};

} // namespace ConcuBinE

#endif
