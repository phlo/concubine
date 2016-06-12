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

/* Program::print (bool) ******************************************************/
void Program::print (bool includePC)
{
  for (word i = 0; i < size(); i++) print(includePC, i);
}

/* Program::print (bool, word) ************************************************/
void Program::print (bool includePC, word pc)
{
  if (includePC)
    {
      /* check if intruction can be referenced by a label */
      if (labels.find(pc) != labels.end())
        cout << labels[pc];
      else
        cout << pc;
    }

  /* instruction symbol */
  InstructionPtr cmd = at(pc);
  cout << "\t" << cmd->getSymbol() << "\t";

  /* print unary instruction's argument */
  if (UnaryInstructionPtr u =
      dynamic_pointer_cast<UnaryInstruction>(cmd))
    {
      if (labels.find(u->arg) != labels.end())
        {
          cout << labels[u->arg];
        }
      else
        {
          cout << u->arg;
        }
    }
}
