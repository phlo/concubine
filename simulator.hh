#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <functional>

#include "common.hh"
#include "instruction.hh"

//==============================================================================
// forward declarations
//==============================================================================

// TODO: forward-declare
#include "program.hh"
#include "trace.hh"

//==============================================================================
// Simulator class
//==============================================================================

struct Simulator
{
  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // list of programs
  //
  Program::List::ptr programs;

  // generated trace
  //
  Trace::ptr trace;

  // bound
  //
  bound_t bound;

  // seed used for random thread scheduling
  //
  uint64_t seed;

  // list of all threads
  //
  std::vector<Thread> threads;

  // list of active threads
  //
  // NOTE: much more lookup than insert/remove operations
  //
  std::vector<Thread *> active;

  // main memory
  //
  // address -> value
  //
  std::unordered_map<word_t, word_t> heap;

  // number of threads containing calls to a specific checkpoint
  //
  // checkpoint id -> list of threads
  //
  std::unordered_map<word_t, std::vector<Thread *>> threads_per_checkpoint;

  // number of threads currently waiting for a specific checkpoint
  //
  // checkpoint id -> number of waiting threads
  //
  std::unordered_map<word_t, word_t> waiting_for_checkpoint;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Simulator (const Program::List::ptr & programs,
             bound_t bound = 0,
             uint64_t seed = 0);

  //----------------------------------------------------------------------------
  // private functions
  //----------------------------------------------------------------------------

  // checks if all threads reached the given checkpoint and resumes them
  //
  void check_and_resume (word_t id);

  // creates a thread using the given program, thread id == number of threads
  //
  word_t create_thread (const Program & program);

  // run the simulator, using the specified scheduler
  //
  Trace::ptr run (std::function<Thread *()> scheduler);

  //----------------------------------------------------------------------------
  // public functions
  //----------------------------------------------------------------------------

  // runs the simulator using a random trace
  //
  static Trace::ptr simulate (const Program::List::ptr & programs,
                              bound_t bound = 0,
                              uint64_t seed = 0);

  // replay the given trace (trace must match simulator configuration)
  //
  static Trace::ptr replay (const Trace & trace, bound_t bound = 0);
};

//==============================================================================
// Thread
//==============================================================================

struct Thread
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  // store buffer
  //
  struct Buffer
    {
      bool full = false;
      word_t address = 0;
      word_t value = 0;
    };

  // thread state
  //
  enum class State : char
  {
    initial   = 'I',  // created, but not started
    running   = 'R',  // running
    flushing  = 'F',  // flushing store buffer
    waiting   = 'W',  // waiting at checkpoint
    halted    = 'H',  // no more instructions or halted
    exited    = 'E'   // exit called
  };

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // thread id
  //
  word_t id;

  // program counter
  //
  word_t pc;

  // special CAS register
  //
  word_t mem;

  // accumulator register
  //
  word_t accu;

  // current (or previous) checkpoint's id
  //
  word_t check;

  // store buffer
  //
  Buffer buffer;

  // thread state
  //
  State state;

  // reference to the simulator owning the thread
  //
  Simulator & simulator;

  // reference to the program being executed
  //
  const Program & program;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Thread (Simulator & simulator, word_t id, const Program & program);

  //----------------------------------------------------------------------------
  // functions
  //----------------------------------------------------------------------------

  // load value from given address
  //
  word_t load (word_t address, bool indirect = false);

  // store given value at address
  //
  void store (word_t address,
              word_t value,
              bool indirect = false,
              bool atomic = false);

  // flush store buffer
  //
  void flush ();

  // execute current instruction
  //
  void execute ();

  // double-dispatched execute functions
  //
  void execute (const Instruction::Load &);
  void execute (const Instruction::Store &);

  void execute (const Instruction::Fence &);

  void execute (const Instruction::Add &);
  void execute (const Instruction::Addi &);
  void execute (const Instruction::Sub &);
  void execute (const Instruction::Subi &);
  void execute (const Instruction::Mul &);
  void execute (const Instruction::Muli &);

  void execute (const Instruction::Cmp &);
  void execute (const Instruction::Jmp &);
  void execute (const Instruction::Jz &);
  void execute (const Instruction::Jnz &);
  void execute (const Instruction::Js &);
  void execute (const Instruction::Jns &);
  void execute (const Instruction::Jnzns &);

  void execute (const Instruction::Mem &);
  void execute (const Instruction::Cas &);

  void execute (const Instruction::Check &);

  void execute (const Instruction::Halt &);
  void execute (const Instruction::Exit &);
};

//==============================================================================
// non-member operators
//==============================================================================

std::ostream & operator << (std::ostream & os, Thread::State state);

#endif
