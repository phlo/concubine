#include "thread.hh"

#include "machine.hh"

/* constructor ****************************************************************/
Thread::Thread (Machine & m, unsigned int & i, Program & p) :
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

/* Thread::load (int &) *******************************************************/
short & Thread::load (int & addr)
{
  return machine.memory[addr];
}

/* Thread::store (int &, short &) *********************************************/
void Thread::store (int & addr, short & val)
{
  machine.memory[addr] = val;
}

/* Thread::execute (void) *****************************************************/
void Thread::execute ()
{
  if (pc < program.size())
    {
      program[pc]->printDebug(*this);
      program[pc]->execute(*this);
    }
  else
    {
      state = Thread::State::STOPPED;
    }
}
