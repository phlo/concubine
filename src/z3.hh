/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

namespace ConcuBinE {

//==============================================================================
// Z3
//==============================================================================

struct Z3 : public Solver
{
  //----------------------------------------------------------------------------
  // public member functions inherited from Solver
  //----------------------------------------------------------------------------

  // get name
  //
  virtual std::string name () const;

  // get version
  //
  virtual std::string version () const;

  // build formula from given encoding (include check-sat for completeness)
  //
  virtual std::string formula (Encoder & encoder) const;

  // evaluate arbitrary formula
  //
  virtual bool sat (const std::string & formula);

  // solve given encoding and return trace
  //
  virtual std::unique_ptr<Trace> solve (Encoder & encoder);
};

} // namespace ConcuBinE

#endif
