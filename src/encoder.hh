/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <map>
#include <sstream>
#include <vector>

#include "instruction.hh"
#include "program.hh"

namespace ConcuBinE {

//==============================================================================
// forward declarations
//==============================================================================

class MMap;

//==============================================================================
// Encoder
//==============================================================================

class Encoder
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public constants
  //----------------------------------------------------------------------------

  // thread state symbols
  //
  static const std::string accu_sym;
  static const std::string mem_sym;
  static const std::string sb_adr_sym;
  static const std::string sb_val_sym;
  static const std::string sb_full_sym;
  static const std::string stmt_sym;
  static const std::string block_sym;
  static const std::string halt_sym;

  // machine state symbols
  //
  static const std::string heap_sym;
  static const std::string exit_flag_sym;
  static const std::string exit_code_sym;

  // transition symbols
  //
  static const std::string thread_sym;
  static const std::string exec_sym;
  static const std::string flush_sym;
  static const std::string check_sym;

  //----------------------------------------------------------------------------
  // public constructors
  //----------------------------------------------------------------------------

  Encoder (const std::shared_ptr<Program::List> & programs,
           const std::shared_ptr<MMap> & mmap,
           size_t bound);

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // main encoding function
  //
  virtual void encode () = 0;

  // double-dispatched instruction encoding functions
  //
  virtual std::string encode (const Instruction::Load &) = 0;
  virtual std::string encode (const Instruction::Store &) = 0;

  virtual std::string encode (const Instruction::Fence &) = 0;

  virtual std::string encode (const Instruction::Add &) = 0;
  virtual std::string encode (const Instruction::Addi &) = 0;
  virtual std::string encode (const Instruction::Sub &) = 0;
  virtual std::string encode (const Instruction::Subi &) = 0;
  virtual std::string encode (const Instruction::Mul &) = 0;
  virtual std::string encode (const Instruction::Muli &) = 0;

  virtual std::string encode (const Instruction::Cmp &) = 0;
  virtual std::string encode (const Instruction::Jmp &) = 0;
  virtual std::string encode (const Instruction::Jz &) = 0;
  virtual std::string encode (const Instruction::Jnz &) = 0;
  virtual std::string encode (const Instruction::Js &) = 0;
  virtual std::string encode (const Instruction::Jns &) = 0;
  virtual std::string encode (const Instruction::Jnzns &) = 0;

  virtual std::string encode (const Instruction::Mem &) = 0;
  virtual std::string encode (const Instruction::Cas &) = 0;

  virtual std::string encode (const Instruction::Check &) = 0;

  virtual std::string encode (const Instruction::Halt &) = 0;
  virtual std::string encode (const Instruction::Exit &) = 0;

  // add exit code assertion
  //
  virtual void assert_exit () = 0;

  //----------------------------------------------------------------------------
  // public data members
  //----------------------------------------------------------------------------

  // pointer to the programs being encoded (index == thread id)
  //
  // std::shared_ptr - forwarded to the solver for generating a Trace
  //
  std::shared_ptr<Program::List> programs;

  // pointer to initial memory layout
  //
  std::shared_ptr<MMap> mmap;

  // bound
  //
  size_t bound;

  // SMT formula buffer
  //
  std::ostringstream formula;

protected: //===================================================================

  //----------------------------------------------------------------------------
  // protected member types
  //----------------------------------------------------------------------------

  // state being updated (to distinguish in Encoder::encode)
  //
  enum class Update
    {
      accu,
      mem,
      sb_adr,
      sb_val,
      heap
    };

  //----------------------------------------------------------------------------
  // protected constants
  //----------------------------------------------------------------------------

  // comments
  //
  static const std::string accu_comment;
  static const std::string mem_comment;
  static const std::string sb_adr_comment;
  static const std::string sb_val_comment;
  static const std::string sb_full_comment;
  static const std::string stmt_comment;
  static const std::string block_comment;
  static const std::string halt_comment;

  static const std::string exit_flag_comment;
  static const std::string exit_code_comment;
  static const std::string heap_comment;

  static const std::string thread_comment;
  static const std::string exec_comment;
  static const std::string flush_comment;
  static const std::string check_comment;

  //----------------------------------------------------------------------------
  // protected member functions
  //----------------------------------------------------------------------------

  // iteration helpers
  //
  template <class Functor>
  void iterate_threads (const Functor & fun)
    {
      for (thread = 0; thread < num_threads; thread++)
        fun();
    }

  template <class Functor>
  void iterate_programs (const Functor & fun)
    {
      thread = 0;
      for (const Program & program : *programs)
        {
          fun(program);
          thread++;
        }
    }

  template <class Functor>
  void iterate_programs_reverse (const Functor & fun)
    {
      thread = num_threads - 1;
      for (auto rit = programs->rbegin(); rit != programs->rend(); ++rit)
        {
          fun(*rit);
          thread--;
        }
    }

  //----------------------------------------------------------------------------
  // protected data members
  //----------------------------------------------------------------------------

  // number of threads (short hand for programs->size())
  //
  size_t num_threads;

  // use Sinz's cardinality constraint (num_threads > 4)
  //
  bool use_sinz_constraint;

  // current thread id
  //
  word_t thread;

  // current pc
  //
  word_t pc;

  // current state being updated
  //
  Update update;

  // list of predecessors for each thread
  //
  // thread -> pc -> set of predecessors
  //
  std::vector<std::unordered_map<word_t, std::set<word_t>>> predecessors;

  // pcs of statements requiring an empty store buffer
  //
  // thread -> list of program counters
  //
  std::map<word_t, std::vector<word_t>> flushes;

  // pcs of checkpoint statements
  //
  // checkpoint id -> thread -> list of program counters
  //
  std::map<word_t, std::map<word_t, std::vector<word_t>>> checkpoints;

  // pcs of halt statements
  //
  // thread -> list of program counters
  //
  std::map<word_t, std::vector<word_t>> halts;

  // pcs of exit calls
  //
  // thread -> list of program counters
  //
  std::map<word_t, std::vector<word_t>> exits;
};

} // namespace ConcuBinE

#endif
