#include "program.hh"

#include <iostream>

using namespace std;

/* constructor ****************************************************************/
Program::Program(string & p) : path(p), syncIDs(), labels()
{
  Parser<Program> parser(p);
  parser.parse(this);
}

/* Program::add (InstructionPtr) **********************************************/
void Program::add (InstructionPtr i)
{
  push_back(i);

  /* collect sync barrier ids */
  if (shared_ptr<Sync> s = dynamic_pointer_cast<Sync>(i))
    syncIDs.insert(s->arg);
}

/* Program::getPath (void) ****************************************************/
string & Program::getPath () { return path; }

/* Program::getSyncIDs (void) *************************************************/
unordered_set<word> & Program::getSyncIDs () { return syncIDs; }

/* Program::getLabels (void) **************************************************/
unordered_map<word, string> & Program::getLabels () { return labels; }
