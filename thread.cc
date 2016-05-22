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
      program[pc]->print(*this);
      program[pc]->execute(*this);
    }
  else
    {
      state = Thread::State::STOPPED;
    }
}
