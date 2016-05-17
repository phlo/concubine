#include "program.hh"

#include <iostream>

using namespace std;

/* constructor ****************************************************************/
Program::Program(string & p) : path(p), syncIDs() {}

/* Program::add (shared_ptr<Instruction>) *************************************/
void Program::add (shared_ptr<Instruction> i)
{
  push_back(i);

  /* collect sync barrier ids */
  if (shared_ptr<Sync> s = dynamic_pointer_cast<Sync>(i))
    {
      syncIDs.insert(s->getArg());
    }
}

/* Program::getPath (void) ****************************************************/
string & Program::getPath ()
{
  return path;
}

/* Program::getSyncIDs (void) *************************************************/
unordered_set<short> & Program::getSyncIDs ()
{
  return syncIDs;
}
