#include "boolector.hh"

#include <iostream>

using namespace std;

/* Boolector::build_command (void) ********************************************/
string Boolector::build_command ()
{
  return "boolector -m";
}

/* Boolector::sat (string &) **************************************************/
bool Boolector::sat (string & formula)
{
  execute(formula);

  cout << std_out;

  return std_out == "sat\n";
}
