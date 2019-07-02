#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

#include <z3++.h>

struct Z3 : public Solver
{
  virtual std::string name () const;

  virtual bool sat (const std::string & formula);

  virtual Schedule::ptr solve (Encoder & encoder,
                               const std::string & constraints);
};

#endif
