#include "program.hh"

#include <iostream>

using namespace std;

/* default constructor ********************************************************/
Program::Program() {}

/* construct from file ********************************************************/
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
  if (SyncPtr s = dynamic_pointer_cast<Sync>(i))
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
  for (word i = 0; i < size(); i++)
    {
      print(includePC, i);
      cout << endl;
    }
}

/* Program::print (bool, word) ************************************************/
void Program::print (bool includePC, word pc)
{
  /* check if instruction can be referenced by a label */
  if (labels.find(pc) != labels.end())
    {
      cout << labels[pc];

      if (includePC)
        cout << "\t";
      else
        cout << ": ";
    }
  else if (includePC)
    cout << pc << "\t";

  /* instruction symbol */
  InstructionPtr cmd = at(pc);
  cout << cmd->getSymbol() << "\t";

  /* print unary instruction's argument */
  if (UnaryInstructionPtr u = dynamic_pointer_cast<UnaryInstruction>(cmd))
    {
      if (dynamic_pointer_cast<Jmp>(cmd) && labels.find(u->arg) != labels.end())
        cout << labels[u->arg];
      else
        cout << u->arg;
    }
}
