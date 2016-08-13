#include "verifier.hh"

#include "smtlib.hh"

/*******************************************************************************
 * Verifier
*******************************************************************************/
Verifier::Verifier (Solver & s, smtlib::Encoder & f, string & spec) :
  solver(s),
  formula(f),
  specification(spec)
{}

/* Verifier::print (void) *****************************************************/
void Verifier::print ()
{
  cout  << formula.toString() << "\n"
        << specification << "\n"
        << smtlib::checkSat() << "\n"
        << smtlib::exit() << "\n";
}

/* Verifier::sat (void) *******************************************************/
bool Verifier::sat ()
{
  string smt =
      formula.toString() + "\n" +
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
