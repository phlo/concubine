#include "boolector.hh"

#include <iostream>

using namespace std;

/* Boolector::buildCommand (void) *********************************************/
string Boolector::buildCommand ()
{
  return "boolector -m";
}

/* Boolector::sat (string &) **************************************************/
bool Boolector::sat (string & formula)
{
  execute(formula);

  cout << stdOut;

  return stdOut == "sat\n";
}
