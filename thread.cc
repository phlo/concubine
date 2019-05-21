#include "thread.hh"

#include "simulator.hh"
#include "program.hh"

using namespace std;

/* constructor ****************************************************************/
Thread::Thread (Simulator & _simulator, unsigned int _id, Program & _program) :
  id(_id),
  pc(0),
  mem(0),
  accu(0),
  check(0),
  state(INITIAL),
  simulator(_simulator),
  program(_program)
{}

/* Thread::load (word) ********************************************************/
word Thread::load (word addr, bool indirect)
{
  return
    indirect
      ? simulator.heap[simulator.heap[addr]]
      : simulator.heap[addr];
}

/* Thread::store (word, word) *************************************************/
void Thread::store (word addr, word val, bool indirect)
{
  simulator.heap[indirect ? simulator.heap[addr] : addr] = val;
}

/* Thread::execute (void) *****************************************************/
void Thread::execute ()
{
  if (pc >= program.size())
    throw runtime_error("illegal pc [" + to_string(pc) + "]");

  /* execute instruction */
  program.at(pc)->execute(*this);

  /* set state to STOPPED if it was the last command in the program */
  if (pc >= program.size())
    state = Thread::State::STOPPED;
}
