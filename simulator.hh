/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef MACHINE_HH_
#define MACHINE_HH_

#include <functional>
#include <unordered_set>

#include "common.hh"
#include "program.hh"

namespace ConcuBinE {

//==============================================================================
// forward declarations
//==============================================================================

class MMap;
class Trace;

//==============================================================================
// Simulator
//==============================================================================

class Simulator
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public member types
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
  // public member functions
  //----------------------------------------------------------------------------

  // simulate given programs using a random scheduler
  //
  std::unique_ptr<Trace> simulate (const std::shared_ptr<Program::List> & programs,
                                   const std::shared_ptr<MMap> & mmap = {},
                                   size_t bound = 0);

  // replay given trace
  //
  std::unique_ptr<Trace> replay (const Trace & trace, size_t bound = 0);

  // double-dispatched execute functions
  //
  template <class Instruction>
  void execute (const Instruction & op);

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // (re)initialize
  //
  void init (const std::shared_ptr<Program::List> & programs,
             const std::shared_ptr<MMap> & mmap,
             size_t bound);

  // get or set program counter
  //
  word_t pc () const;
  void pc (word_t value);
  void pc_increment ();

  // get or set accumulator register
  //
  word_t accu () const;
  void accu (word_t value);

  // get or set special CAS register
  //
  word_t mem () const;
  void mem (word_t value);

  // get or set store buffer address
  //
  word_t sb_adr () const;
  void sb_adr (word_t value);

  // get or set store buffer value
  //
  word_t sb_val () const;
  void sb_val (word_t value);

  // get or set store buffer full flag
  //
  bool sb_full () const;
  void sb_full (bool value);

  // load value from given address
  //
  word_t load (word_t address);
  word_t load (word_t address, bool indirect);

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

  // run simulator with given scheduler
  //
  std::unique_ptr<Trace> run (std::function<void()> scheduler);

  //----------------------------------------------------------------------------
  // private data members
  //----------------------------------------------------------------------------

  // Mersenne Twister pseudo-random number generator
  //
  std::mt19937_64 random;

  // list of programs
  //
  const Program::List * programs;

  // generated trace
  //
  std::unique_ptr<Trace> trace;

  // bound
  //
  size_t bound;

  // current step
  //
  size_t step;

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
  // checkpoint id -> number of threads
  //
  std::unordered_map<word_t, word_t> waiting_for_checkpoint;
};

//==============================================================================
// non-member operators
//==============================================================================

std::ostream & operator << (std::ostream & os, Simulator::State state);

} // namespace ConcuBinE

#endif
