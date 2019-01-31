#ifndef BTORMC_HH
#define BTORMC_HH

#include "solver.hh"

struct BtorMC : public Solver
{
  virtual std::string build_command (void);

  virtual std::string build_formula (Encoder &, std::string &);

  virtual SchedulePtr build_schedule (void);
};

typedef std::shared_ptr<BtorMC> BtorMCPtr;

#endif
