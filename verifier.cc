#include "verifier.hh"

#include "encoder.hh"
#include "smtlib.hh"
#include "solver.hh"

using namespace std;

/*******************************************************************************
 * Verifier
*******************************************************************************/
Verifier::Verifier (Solver & s, Encoder & f, string & c) :
  solver(s),
  formula(f),
  constraints(c)
{}

/* Verifier::print (void) *****************************************************/
void Verifier::print ()
{
  cout  << formula.str()
        << (constraints.empty()
          ? ""
          : (verbose ? smtlib::comment_section("additional constraints") : "") +
            constraints + eol)
        << smtlib::check_sat() << "\n"
        << smtlib::exit() << "\n";
}

/* Verifier::sat (void) *******************************************************/
bool Verifier::sat ()
{
  string smt =
      formula.str() +
      (constraints.empty() ? "" : constraints + "\n") +
      smtlib::check_sat() + "\n" +
      smtlib::exit();

  return solver.sat(smt);
}

/* Verifier::get_schedule (void) **********************************************/
SchedulePtr Verifier::get_schedule ()
{
  return nullptr;
}
