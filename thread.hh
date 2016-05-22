#ifndef THREAD_HH_
#define THREAD_HH_

#include "common.hh"
#include "program.hh"

/* forward declerations */
class Machine;

/*******************************************************************************
 * Thread
 ******************************************************************************/
struct Thread
{
  enum State
  {
    INITIAL,  // created, but not started
    RUNNING,  // running
    WAITING,  // waiting for other thread(s) (syncing)
    STOPPED,  // no more instructions or halted
    EXITING   // exit called
  };

  unsigned int  id;       // thread id
  word          pc;       // program counter
  word          mem;      // special CAS register
  word          accu;     // accumulator register
  word          sync;     // current (or previous) barrier's id
  word          exitCode; // TODO: really neccessary?
  State         state;    // thread state
  Machine &     machine;  // reference to the machine owning the thread
  Program &     program;  // reference to the program being executed

  Thread (Machine &, unsigned int, Program &);

  word          load (word);
  void          store (word, word);

  virtual void  execute (void);
};

/*******************************************************************************
 * ThreadPtr
 ******************************************************************************/
typedef shared_ptr<Thread> ThreadPtr;

#endif
