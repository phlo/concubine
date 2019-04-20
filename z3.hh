#ifndef Z3_HH_
#define Z3_HH_

#include "solver.hh"

class Z3 : public Solver
{
  virtual std::string build_command ();

  virtual std::optional<Variable> parse_line (std::istringstream & line);

public:

  virtual std::string name ();

  virtual bool sat (std::string & formula);

  virtual SchedulePtr solve (Encoder & encoder, std::string & constraints);
};

typedef std::shared_ptr<Z3> Z3Ptr;

#endif
