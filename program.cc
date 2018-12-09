#include "program.hh"

#include <sstream>

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Program::Program() {}

/* construct from file ********************************************************/
Program::Program(string p) : path(p), sync_ids(), labels()
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
    sync_ids.insert(s->arg);
}

/* Program::print (bool) ******************************************************/
string Program::print (bool include_pc)
{
  ostringstream ss;

  for (word i = 0; i < size(); i++)
    ss <<  print(include_pc, i);

  return ss.str();
}

/* Program::print (bool, word) ************************************************/
string Program::print (bool include_pc, word pc)
{
  ostringstream ss;

  /* check if instruction can be referenced by a label */
  if (labels.find(pc) != labels.end())
    {
      ss << labels[pc];

      if (include_pc)
        ss << "\t";
      else
        ss << ": ";
    }
  else if (include_pc)
    ss << pc << "\t";

  /* instruction symbol */
  InstructionPtr cmd = at(pc);
  ss << cmd->get_symbol() << "\t";

  /* print unary instruction's argument */
  if (UnaryInstructionPtr u = dynamic_pointer_cast<UnaryInstruction>(cmd))
    {
      if (dynamic_pointer_cast<Jmp>(cmd) && labels.find(u->arg) != labels.end())
        ss << labels[u->arg];
      else if (auto m = dynamic_pointer_cast<MemoryInstruction>(u))
        ss << (m->indirect ? "[" : "") << m->arg << (m->indirect ? "]" : "");
      else
        ss << u->arg;
    }

  return ss.str();
}
