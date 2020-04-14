#ifndef BTORMC_HH
#define BTORMC_HH

#include "boolector.hh"

namespace ConcuBinE {

//==============================================================================
// BtorMC
//==============================================================================

class BtorMC : public Boolector
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public member functions inherited from Solver
  //----------------------------------------------------------------------------

  // get name
  //
  virtual std::string name () const;

  // build formula from given encoding
  //
  virtual std::string formula (Encoder & encoder) const;

  // evaluate arbitrary formula
  //
  using Boolector::sat;

  virtual bool sat (const std::string & formula, size_t bound);

  // solve given encoding and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder);

  //----------------------------------------------------------------------------
  // public member functions inherited from External
  //----------------------------------------------------------------------------

  // get command line
  //
  virtual const std::vector<std::string> & command () const;

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member functions inherited from External
  //----------------------------------------------------------------------------

  // parse current variable's symbol
  //
  virtual Symbol symbol (std::istringstream &);

  // parse variable
  //
  virtual Symbol parse (std::istringstream &);

  //----------------------------------------------------------------------------
  // private data members
  //----------------------------------------------------------------------------

  // bound for setting -kmax
  //
  std::string kmax = "20";
};

} // namespace ConcuBinE

#endif
