#ifndef THREAD_HH_
#define THREAD_HH_

#include <deque>
#include <memory>
#include <iostream>

#include "common.hh"
#include "program.hh"

/* forward declarations */
struct Simulator;

/*******************************************************************************
 * ThreadID
 ******************************************************************************/
typedef unsigned long ThreadID;

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

  Thread (Simulator &, unsigned int, Program &);

  ThreadID      id;         // thread id
  word          pc;         // program counter
  word          mem;        // special CAS register
  word          accu;       // accumulator register
  word          sync;       // current (or previous) barrier's id
  State         state;      // thread state
  Simulator &   simulator;  // reference to the simulator owning the thread
  Program &     program;    // pointer to the program being executed

  word          load (word, bool);
  void          store (word, word, bool);

  virtual void  execute (void);
};

/*******************************************************************************
 * ThreadPtr
 ******************************************************************************/
typedef std::shared_ptr<Thread> ThreadPtr;

/*******************************************************************************
 * ThreadList
 ******************************************************************************/
typedef std::deque<ThreadPtr> ThreadList;

#endif
