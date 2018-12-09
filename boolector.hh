#ifndef BOOLECTOR_HH_
#define BOOLECTOR_HH_

#include "solver.hh"

/*******************************************************************************
 * Boolector
 ******************************************************************************/
class Boolector : public Solver
{
  virtual std::string   build_command (void);

public:
  virtual bool          sat (std::string &);
};

/*******************************************************************************
 * BoolectorPtr
 ******************************************************************************/
typedef std::shared_ptr<Boolector> BoolectorPtr;

#endif
