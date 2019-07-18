#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <functional>

#include "common.hh"
#include "instruction.hh"

// TODO: forward-declare
#include "program.hh"
#include "trace.hh"

namespace ConcuBinE {

//==============================================================================
// forward declarations
//==============================================================================

//==============================================================================
// Simulator class
//==============================================================================

struct Simulator
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

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

  // list of programs
  //
  Program::List::ptr programs;

  // generated trace
  //
  Trace::ptr trace;

  // current step
  //
  size_t step;

  // bound
  //
  size_t bound;

  // current thread
  //
  word_t thread;

  // list of thread states
  //
  std::vector<State> state;

  // list of active threads
  //
  // NOTE: much more lookup than insert/remove operations
  //
  std::vector<word_t> active;

  // threads containing calls to a specific checkpoint
  //
  // checkpoint id -> list of threads
  //
  std::unordered_map<word_t, std::unordered_set<word_t>> threads_per_checkpoint;

  // threads waiting for a specific checkpoint
  //
  // checkpoint id -> list of threads
  //
  std::unordered_map<word_t, std::unordered_set<word_t>> waiting_for_checkpoint;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Simulator (const Program::List::ptr & programs, size_t bound = 0);

  //----------------------------------------------------------------------------
  // private functions
  //----------------------------------------------------------------------------

  // program counter
  //
  word_t pc () const;
  void pc (word_t value);
  void pc_increment ();

  // accumulator register
  //
  word_t accu () const;
  void accu (word_t value);

  // special CAS register
  //
  word_t mem () const;
  void mem (word_t value);

  // store buffer address
  //
  word_t sb_adr () const;
  void sb_adr (word_t value);

  // store buffer value
  //
  word_t sb_val () const;
  void sb_val (word_t value);

  // store buffer full flag
  //
  bool sb_full () const;
  void sb_full (bool value);

  // load value from given address
  //
  word_t load (word_t address, bool indirect = false);

  // store given value at address
  //
  void store (word_t address,
              word_t value,
              bool indirect = false,
              bool flush = false);

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

  // checks if all threads reached the given checkpoint and resumes them
  //
  void check_and_resume (word_t id);

  // run the simulator, using the specified scheduler
  //
  Trace::ptr run (std::function<word_t()> scheduler);

  //----------------------------------------------------------------------------
  // public functions
  //----------------------------------------------------------------------------

  // runs the simulator using a random trace
  //
  static Trace::ptr simulate (const Program::List::ptr & programs,
                              size_t bound = 0);

  // replay the given trace (trace must match simulator configuration)
  //
  static Trace::ptr replay (const Trace & trace, size_t bound = 0);
};

//==============================================================================
// non-member operators
//==============================================================================

std::ostream & operator << (std::ostream & os, Simulator::State state);

} // namespace ConcuBinE

#endif
