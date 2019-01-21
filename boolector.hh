#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

struct Boolector : public Solver
{
  virtual std::string build_command (void);

  virtual std::string build_formula (Encoder &, std::string &);

  virtual SchedulePtr build_schedule (void);
};

typedef std::shared_ptr<Boolector> BoolectorPtr;

#endif
