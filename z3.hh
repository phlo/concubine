#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

#include <z3++.h>

class Z3 : public Solver
{
  z3::context context;
  z3::solver  solver;

  SchedulePtr build_schedule (ProgramListPtr programs, unsigned long bound);

  // bool get_exec (unsigned long step, word thread, word pc);
  // word get_accu (unsigned long step, word thread);
  // word get_mem (unsigned long step, word thread);
  // std::optional<Schedule::Heap_Cell> get_heap_update (unsigned long step, word thread, word pc);

  z3::expr bool_var (std::string name);
  z3::expr bv_var (std::string name);
  z3::expr heap_var (unsigned long step);

public:

  Z3 ();

  virtual std::string name ();

  virtual bool sat (std::string & formula);

  virtual SchedulePtr solve (Encoder & encoder, std::string & constraints);
};

typedef std::shared_ptr<Z3> Z3Ptr;

#endif
