/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

namespace ConcuBinE {

//==============================================================================
// Boolector
//==============================================================================

class Boolector : public External
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public member functions inherited from Solver
  //----------------------------------------------------------------------------

  // get name
  //
  virtual std::string name () const;

  // get version
  //
  virtual std::string version () const;

  // build formula from given encoding
  //
  virtual std::string formula (Encoder & encoder) const;

  //----------------------------------------------------------------------------
  // public member functions inherited from External
  //----------------------------------------------------------------------------

  // get command line
  //
  virtual std::vector<std::string> command () const;

protected: //===================================================================

  //----------------------------------------------------------------------------
  // protected member functions inherited from External
  //----------------------------------------------------------------------------

  // parse variable
  //
  virtual Symbol parse (std::istringstream & line);
};

} // namespace ConcuBinE

#endif
