#ifndef VERIFIER_HH_
#define VERIFIER_HH_

#include <memory>

#include "solver.hh"
#include "encoder.hh"
#include "schedule.hh"

/*******************************************************************************
 * Verifier
*******************************************************************************/
class Verifier
{
  /* wrapper to external smt solver */
  Solver &            solver;

  /* smt encoder, storing the formula */
  smtlib::Encoder &   formula;

  /* specification in SMT-Lib v2 format */
  string &            specification;

public:
  Verifier (Solver &, smtlib::Encoder &, string &);

  /* print the complete (formula + specification) SMT-Lib v2 file to stdout */
  void                print (void);

  /* calls solver and returns result */
  bool                sat (void);

  /* returns conflicting Schedule if solver returns SAT and null otherwise */
  SchedulePtr         getSchedule (void);
};

/*******************************************************************************
 * VerifierPtr
 ******************************************************************************/
typedef shared_ptr<Verifier> VerifierPtr;

#endif
