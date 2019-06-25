#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <functional>
#include <memory>
#include <unordered_map>

#include "common.hh"
#include "instructionset.hh"

// TODO: forward-declare
#include "program.hh"
#include "schedule.hh"

struct Simulator
{
  /* list of programs */
  Program_list_ptr          programs;

  Schedule_ptr              schedule;

  /* bounded execution */
  bound_t                   bound;

  /* seed used for thread scheduling */
  uint64_t                  seed;

  /* list of active threads */
  // NOTE: much more lookup than insert/remove operations
  std::vector<Thread *>     active;

  /* list of all threads */
  std::vector<Thread>       threads;

  /* main memory */
  std::unordered_map<
    word_t,
    word_t>                 heap;

  /* number of threads containing calls to a specific checkpoint */
  std::unordered_map<
    word_t,
    std::vector<Thread *>>  threads_per_checkpoint;

  /* number of threads currently waiting for a specific checkpoint */
  std::unordered_map<
    word_t,
    word_t>                 waiting_for_checkpoint;

  /*****************************************************************************
   * constructors
   ****************************************************************************/

  /* default constructor (testing only) */
  Simulator ();

  /* constructs a new simulator for simulation */
  Simulator (Program_list_ptr programs, bound_t bound = 0, uint64_t seed = 0);

  /*****************************************************************************
   * private functions
   ****************************************************************************/

  /* checks if all threads reached the given checkpoint and resumes them */
  void                      check_and_resume (word_t id);

  /* creates a thread using the given program, thread id == number of threads*/
  word_t                    create_thread (Program &);

  /* run the simulator, using the specified scheduler */
  Schedule_ptr              run (std::function<Thread *()>);

  /*****************************************************************************
   * public functions
   ****************************************************************************/

  /* runs the simulator using a random schedule */
  static Schedule_ptr       simulate (
                                      const Program_list_ptr programs,
                                      const bound_t bound = 0,
                                      const uint64_t seed = 0
                                     );

  /* replay the given schedule (schedule must match simulator configuration) */
  static Schedule_ptr       replay (
                                    const Schedule &,
                                    const bound_t bound = 0
                                   );
};

using Simulator_ptr = std::shared_ptr<Simulator>;

struct Thread
{
  struct Buffer
    {
      bool full = false;
      word_t address = 0;
      word_t value = 0;
    };

  enum class State : char
  {
    initial   = 'I',  // created, but not started
    running   = 'R',  // running
    flushing  = 'F',  // flushing store buffer
    waiting   = 'W',  // waiting at checkpoint
    halted    = 'H',  // no more instructions or halted
    exited    = 'E'   // exit called
  };

  word_t        id;         // thread id
  word_t        pc;         // program counter
  word_t        mem;        // special CAS register
  word_t        accu;       // accumulator register
  word_t        check;      // current (or previous) checkpoint's id
  Buffer        buffer;     // store buffer
  State         state;      // thread state
  Simulator &   simulator;  // reference to the simulator owning the thread
  Program &     program;    // reference to the program being executed

  Thread (Simulator & simulator, word_t id, Program & program);

  word_t        load (word_t address, const bool indirect = false);
  void          store (
                       word_t address,
                       const word_t value,
                       const bool indirect = false,
                       const bool atomic = false
                      );

  void          flush ();
  void          execute ();

  /* double-dispatched execute functions */
  void          execute (Load &);
  void          execute (Store &);

  void          execute (Fence &);

  void          execute (Add &);
  void          execute (Addi &);
  void          execute (Sub &);
  void          execute (Subi &);
  void          execute (Mul &);
  void          execute (Muli &);

  void          execute (Cmp &);
  void          execute (Jmp &);
  void          execute (Jz &);
  void          execute (Jnz &);
  void          execute (Js &);
  void          execute (Jns &);
  void          execute (Jnzns &);

  void          execute (Mem &);
  void          execute (Cas &);

  void          execute (Check &);

  void          execute (Halt &);
  void          execute (Exit &);
};

std::ostream & operator << (std::ostream & os, Thread::State s);

#endif
