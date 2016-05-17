#ifndef THREAD_HH_
#define THREAD_HH_

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
  unsigned int  pc;       // program counter
  short         mem;      // special CAS register
  short         accu;     // accumulator register
  short         sync;     // current (or previous) barrier's id
  int           exitCode; // TODO: really neccessary?
  State         state;    // thread state
  Machine &     machine;  // reference to the machine owning the thread
  Program &     program;  // reference to the program being executed

  Thread (Machine &, unsigned int &, Program &);

  short &       load (int &);
  void          store (int &, short &);

  virtual void  execute (void);
};

/*******************************************************************************
 * ThreadPtr
 ******************************************************************************/
typedef shared_ptr<Thread> ThreadPtr;

#endif
