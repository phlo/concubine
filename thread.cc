#include "thread.hh"

#include "machine.hh"
#include "program.hh"

using namespace std;

/* constructor ****************************************************************/
Thread::Thread (Machine & m, unsigned int i, Program & p) :
  id(i),
  pc(0),
  mem(0),
  accu(0),
  sync(0),
  state(INITIAL),
  machine(m),
  program(p)
{}

/* Thread::load (word) ********************************************************/
word Thread::load (word addr, bool indirect)
{
  return indirect ? machine.memory[machine.memory[addr]] : machine.memory[addr];
}

/* Thread::store (word, word) *************************************************/
void Thread::store (word addr, word val, bool indirect)
{
  if (indirect)
    machine.memory[machine.memory[addr]] = val;
  else
    machine.memory[addr] = val;
}

/* Thread::execute (void) *****************************************************/
void Thread::execute ()
{
  if (pc >= program.size())
    throw runtime_error("illegal pc [" + to_string(pc) + "]");

  /* print thread id */
  cout << id;

  /* verbose enabled */
  if (verbose)
    {
      cout << "\t";

      /* print instruction details */
      cout << program.print(true, pc);
    }

  /* execute instruction */
  program[pc]->execute(*this);

  /* print accu */
  if (verbose)
    cout << "\t" << accu;

  cout << endl;

  /* set state to STOPPED if it was the last command in the program */
  if (pc >= program.size())
    state = Thread::State::STOPPED;
}
