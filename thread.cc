#include "thread.hh"

#include "machine.hh"

/* constructor ****************************************************************/
Thread::Thread (Machine & m, unsigned int i, Program & p) :
  id(i),
  pc(0),
  mem(0),
  accu(0),
  sync(0),
  exitCode(0),
  state(INITIAL),
  machine(m),
  program(p)
{}

/* Thread::load (word) ********************************************************/
word Thread::load (word addr)
{
  return machine.memory[addr];
}

/* Thread::store (word, word) *************************************************/
void Thread::store (word addr, word val)
{
  machine.memory[addr] = val;
}

/* Thread::execute (void) *****************************************************/
void Thread::execute ()
{
  if (pc < program.size())
    {
      printInstruction();
      program[pc]->execute(*this);
    }
  else
    {
      state = Thread::State::STOPPED;
    }
}

/* Thread::printInstruction (void) ********************************************/
void Thread::printInstruction (void)
{
  unordered_map<word, string> & labels = program.getLabels();

  /* print thread id */
  cout << id;

  /* verbose enabled */
  if (verbose)
    {
      cout << "\t";

      /* current pc has label */
      if (labels.find(pc) != labels.end())
        cout << labels[pc];
      else
        cout << pc;

      /* instruction symbol */
      cout << "\t" << program[pc]->getSymbol() << "\t";

      /* print unary instruction's argument */
      if (UnaryInstructionPtr u =
          dynamic_pointer_cast<UnaryInstruction>(program[pc]))
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

  cout << endl;
}
