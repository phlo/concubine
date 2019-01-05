#include "boolector.hh"

#include <iostream>

using namespace std;

string Boolector::build_command ()
{
  return "boolector -m";
}

bool Boolector::sat (string & formula)
{
  execute(formula);

  return !std_out.compare(0, 3, "sat");
}
