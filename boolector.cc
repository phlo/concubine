#include "boolector.hh"

/* Boolector::buildCommand (void) *********************************************/
string Boolector::buildCommand ()
{
  return "boolector -m | grep sat";
}

/* Boolector::sat (string &) **************************************************/
bool Boolector::sat (string & formula)
{
  execute(formula);

  cout << stdOut;

  return stdOut == "sat";
}
