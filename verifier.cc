#include "verifier.hh"

#include "smtlib.hh"
#include "solver.hh"
#include "encoder.hh"

using namespace std;

/*******************************************************************************
 * Verifier
*******************************************************************************/
Verifier::Verifier (Solver & s, Encoder & f, string & spec) :
  solver(s),
  formula(f),
  specification(spec)
{}

/* Verifier::print (void) *****************************************************/
void Verifier::print ()
{
  cout  << formula.to_string()
        << specification << "\n"
        << smtlib::check_sat() << "\n"
        << smtlib::exit() << "\n";
}

/* Verifier::sat (void) *******************************************************/
bool Verifier::sat ()
{
  string smt =
      formula.to_string() +
      specification + "\n" +
      smtlib::check_sat() + "\n" +
      smtlib::exit();

  return solver.sat(smt);
}

/* Verifier::get_schedule (void) **********************************************/
SchedulePtr Verifier::get_schedule ()
{
  return nullptr;
}
