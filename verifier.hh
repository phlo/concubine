#ifndef VERIFIER_HH_
#define VERIFIER_HH_

#include <memory>

#include "schedule.hh"

/* forward declarations */
struct Solver;
struct SMTLibEncoder;

/*******************************************************************************
 * Verifier
*******************************************************************************/
struct Verifier
{
  /* constructs a verifier, using the given solver, formula and specification */
  Verifier (Solver &, SMTLibEncoder &, std::string &);

  /* wrapper to external smt solver */
  Solver &            solver;

  /* smt encoder, storing the formula */
  SMTLibEncoder &   formula;

  /* specification in SMT-Lib v2 format */
  std::string &       specification;

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
typedef std::shared_ptr<Verifier> VerifierPtr;

#endif
