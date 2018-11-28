#include "verifier.hh"

#include "smtlib.hh"
#include "solver.hh"
#include "encoder.hh"

using namespace std;

/*******************************************************************************
 * Verifier
*******************************************************************************/
Verifier::Verifier (Solver & s, SMTLibEncoder & f, string & spec) :
  solver(s),
  formula(f),
  specification(spec)
{}

/* Verifier::print (void) *****************************************************/
void Verifier::print ()
{
  cout  << formula.toString()
        << specification << "\n"
        << smtlib::checkSat() << "\n"
        << smtlib::exit() << "\n";
}

/* Verifier::sat (void) *******************************************************/
bool Verifier::sat ()
{
  string smt =
      formula.toString() +
      specification + "\n" +
      smtlib::checkSat() + "\n" +
      smtlib::exit();

  return solver.sat(smt);
}

/* Verifier::getSchedule (void) ***********************************************/
SchedulePtr Verifier::getSchedule ()
{
  return nullptr;
}
