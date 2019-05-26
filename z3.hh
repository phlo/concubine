#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

#include <z3++.h>

struct Z3 : public Solver
{
  virtual std::string name () const;

  virtual bool sat (std::string & formula);

  virtual Schedule_ptr solve (Encoder & encoder, std::string & constraints);
};

typedef std::shared_ptr<Z3> Z3Ptr;

#endif
