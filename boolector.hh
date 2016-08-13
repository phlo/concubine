#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "verifier.hh"

/*******************************************************************************
 * Boolector
 ******************************************************************************/
class Boolector : public Solver
{
  virtual string  buildCommand (void);

public:
  virtual bool    sat (string &);
};

/*******************************************************************************
 * BoolectorPtr
 ******************************************************************************/
typedef shared_ptr<Boolector> BoolectorPtr;

#endif
