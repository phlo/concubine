#ifndef BTORMC_HH
#define BTORMC_HH

#include "boolector.hh"

namespace ConcuBinE {

struct BtorMC : public Boolector
{
  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  size_t bound = 20;

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // return btormc's name
  //
  virtual std::string name () const;

  // build command line for running btormc
  //
  virtual const std::vector<std::string> & command () const;

  // parse current variable's symbol
  //
  virtual Symbol symbol (std::istringstream &);

  // parse variable
  //
  virtual Symbol parse (std::istringstream &);

  // evaluate arbitrary formula
  //
  using Boolector::sat;

  virtual bool sat (const std::string & formula, size_t bound);

  // run btormc and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder);
};

} // namespace ConcuBinE

#endif
