#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

struct Z3 : public SMTLibSolver
{
  virtual std::string build_command (void);

  virtual SchedulePtr build_schedule (void);
};

typedef std::shared_ptr<Z3> Z3Ptr;

#endif
