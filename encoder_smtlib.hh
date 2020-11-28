/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef ENCODER_SMTLIB_HH_
#define ENCODER_SMTLIB_HH_

#include "encoder.hh"

namespace ConcuBinE::smtlib {

//==============================================================================
// SMT-Lib v2.5 Encoder
//==============================================================================

class Encoder : public ConcuBinE::Encoder
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public constants
  //----------------------------------------------------------------------------

  // exit code variable
  //
  static const std::string & exit_code_var;

  //----------------------------------------------------------------------------
  // public constructors
  //----------------------------------------------------------------------------

  Encoder (const std::shared_ptr<Program::List> & programs,
           const std::shared_ptr<MMap> & mmap,
           size_t bound);

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // thread state variable name generators
  //
  static std::string accu_var (word_t step, word_t thread);
  static std::string mem_var (word_t step, word_t thread);
  static std::string sb_adr_var (word_t step, word_t thread);
  static std::string sb_val_var (word_t step, word_t thread);
  static std::string sb_full_var (word_t step, word_t thread);
  static std::string stmt_var (word_t step, word_t thread, word_t pc);
  static std::string block_var (word_t step, word_t thread, word_t id);
  static std::string halt_var (word_t step, word_t thread);

  // machine state variable name generators
  //
  static std::string heap_var (word_t step);
  static std::string exit_flag_var (word_t step);

  // transition variable name generators
  //
  static std::string thread_var (word_t step, word_t thread);
  static std::string exec_var (word_t step, word_t thread, word_t pc);
  static std::string flush_var (word_t step, word_t thread);
  static std::string check_var (word_t step, word_t id);

  //----------------------------------------------------------------------------
  // public member functions inherited from ConcuBinE::Encoder
  //----------------------------------------------------------------------------

  // main encoding function
  //
  virtual void encode ();

  // add exit code assertion
  //
  virtual void assert_exit ();

protected: //===================================================================

  //----------------------------------------------------------------------------
  // protected constants
  //----------------------------------------------------------------------------

  // bitvector sort declaration
  //
  static const std::string bv_sort;

  // variable comments
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

  // thread state variable name generators
  //
  std::string accu_var () const;
  std::string mem_var () const;
  std::string sb_adr_var () const;
  std::string sb_val_var () const;
  std::string sb_full_var () const;
  std::string stmt_var () const;
  std::string halt_var () const;

  // machine state variable name generators
  //
  std::string heap_var () const;
  std::string exit_flag_var () const;

  // transition variable name generators
  //
  std::string thread_var () const;
  std::string exec_var () const;
  std::string flush_var () const;

  // assignment expression generator
  //
  std::string assign (const std::string & variable,
                      const std::string & expression) const;

  //----------------------------------------------------------------------------
  // protected member functions inherited from ConcuBinE::Encoder
  //----------------------------------------------------------------------------

  // state variable definitions
  //
  virtual void define_states () = 0;

  // double-dispatched instruction encoding functions
  //
  virtual std::string encode (const Instruction::Load &);
  virtual std::string encode (const Instruction::Store &);

  virtual std::string encode (const Instruction::Fence &);

  virtual std::string encode (const Instruction::Add &);
  virtual std::string encode (const Instruction::Addi &);
  virtual std::string encode (const Instruction::Sub &);
  virtual std::string encode (const Instruction::Subi &);
  virtual std::string encode (const Instruction::Mul &);
  virtual std::string encode (const Instruction::Muli &);

  virtual std::string encode (const Instruction::Cmp &);
  virtual std::string encode (const Instruction::Jmp &);
  virtual std::string encode (const Instruction::Jz &);
  virtual std::string encode (const Instruction::Jnz &);
  virtual std::string encode (const Instruction::Js &);
  virtual std::string encode (const Instruction::Jns &);
  virtual std::string encode (const Instruction::Jnzns &);

  virtual std::string encode (const Instruction::Mem &);
  virtual std::string encode (const Instruction::Cas &);

  virtual std::string encode (const Instruction::Check &);

  virtual std::string encode (const Instruction::Halt &);
  virtual std::string encode (const Instruction::Exit &);

  //----------------------------------------------------------------------------
  // protected data members
  //----------------------------------------------------------------------------

  // current step
  //
  size_t step;

  // previous step (reduce subtractions)
  //
  size_t prev;

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // load expression generator
  //
  std::string load (word_t address, bool indirect = false);

  // state variable declarations
  //
  void declare_accu ();
  void declare_mem ();
  void declare_sb_adr ();
  void declare_sb_val ();
  void declare_sb_full ();
  void declare_stmt ();
  void declare_block ();
  void declare_halt ();

  void declare_heap ();
  void declare_exit_flag ();
  void declare_exit_code ();

  void declare_states (); // all of the above

  // transition variable declarations
  //
  void declare_thread ();
  void declare_exec ();
  void declare_flush ();
  void declare_check ();

  void declare_transitions (); // all of the above

  // state variable initializers
  //
  void init_accu ();
  void init_mem ();
  void init_sb_adr ();
  void init_sb_val ();
  void init_sb_full ();
  void init_stmt ();
  void init_block ();
  void init_halt ();

  void init_heap ();
  void init_exit_flag ();

  void init_states (); // all of the above

  // transition variable definitions
  //
  void define_exec ();
  void define_check ();

  void define_transitions (); // all of the above

  // constraint definitions
  //
  void define_scheduling_constraints ();
  void define_store_buffer_constraints ();
  void define_checkpoint_constraints ();
  void define_halt_constraints ();

  void define_constraints (); // all of the above
};

} // namespace ConcuBinE::smtlib

#endif
