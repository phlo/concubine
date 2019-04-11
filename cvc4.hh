#ifndef CVC4_HH_
#define CVC4_HH_

#include "solver.hh"

struct CVC4 : public SMTLibSolver
{
  virtual std::string build_command (void);

  virtual SchedulePtr build_schedule (void);
};

typedef std::shared_ptr<CVC4> CVC4Ptr;

#endif
