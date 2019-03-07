#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

struct Boolector : public SMTLibSolver
{
  virtual std::string build_command (void);

  virtual SchedulePtr build_schedule (void);
};

typedef std::shared_ptr<Boolector> BoolectorPtr;

#endif
