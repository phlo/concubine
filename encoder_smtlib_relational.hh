#ifndef ENCODER_SMTLIB_RELATIONAL_HH_
#define ENCODER_SMTLIB_RELATIONAL_HH_

#include "encoder_smtlib.hh"

namespace ConcuBinE::smtlib {

//==============================================================================
// SMT-Lib v2.5 Relational Encoder
//==============================================================================

class Relational : public Encoder
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public constructors
  //----------------------------------------------------------------------------

  // expose constructors from ConcuBinE::smtlib::Encoder
  //
  using Encoder::Encoder;

  //----------------------------------------------------------------------------
  // public member functions inherited from ConcuBinE::smtlib::Encoder
  //----------------------------------------------------------------------------

  // main encoding function
  //
  using Encoder::encode;

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member types
  //----------------------------------------------------------------------------

  // captures frequently used expressions
  //
  struct State
    {
      std::shared_ptr<std::string> accu;
      std::shared_ptr<std::string> mem;
      std::shared_ptr<std::string> sb_adr;
      std::shared_ptr<std::string> sb_val;
      std::shared_ptr<std::string> sb_full;
      std::shared_ptr<std::string> stmt;
      std::shared_ptr<std::string> block;
      std::shared_ptr<std::string> halt;
      std::shared_ptr<std::string> heap;
      std::shared_ptr<std::string> exit_flag;
      std::shared_ptr<std::string> exit_code;

      State () = default;
      State (Relational & encoder);

      operator std::string () const;
    };

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // asserted implication expression generator
  //
  std::string imply (const std::string & ante, const std::string & cons) const;

  // state update helpers
  //
  template <class T>
  std::shared_ptr<std::string> set_accu (const T & op);
  std::shared_ptr<std::string> restore_accu () const;

  template <class T>
  std::shared_ptr<std::string> set_mem (const T & op);
  std::shared_ptr<std::string> restore_mem () const;

  template <class T>
  std::shared_ptr<std::string> set_sb_adr (const T & op);
  std::shared_ptr<std::string> restore_sb_adr () const;

  template <class T>
  std::shared_ptr<std::string> set_sb_val (const T & op);
  std::shared_ptr<std::string> restore_sb_val () const;

  std::shared_ptr<std::string> set_sb_full () const;
  std::shared_ptr<std::string> reset_sb_full () const;
  std::shared_ptr<std::string> restore_sb_full () const;

  std::shared_ptr<std::string> set_stmt (word_t pc);
  template <class T>
  std::shared_ptr<std::string> set_stmt_jmp (const T & op);
  std::shared_ptr<std::string> set_stmt_next ();
  std::shared_ptr<std::string> restore_stmt ();

  template <class T>
  std::shared_ptr<std::string> set_block (const T & op) const;
  std::string reset_block (word_t id) const;
  std::shared_ptr<std::string> restore_block () const;

  std::shared_ptr<std::string> set_halt () const;
  std::shared_ptr<std::string> restore_halt () const;

  template <class T>
  std::shared_ptr<std::string> set_heap (const T & op);
  std::shared_ptr<std::string> restore_heap () const;

  std::shared_ptr<std::string> set_exit_flag () const;
  std::shared_ptr<std::string> unset_exit_flag () const;

  std::shared_ptr<std::string> set_exit_code (word_t e) const;

  // machine state implications
  //
  void imply_thread_executed ();
  void imply_thread_not_executed ();
  void imply_thread_flushed ();
  void imply_machine_exited ();

  //----------------------------------------------------------------------------
  // private member functions inherited from ConcuBinE::smtlib::Encoder
  //----------------------------------------------------------------------------

  // state variable definitions
  //
  virtual void define_states ();

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
  // private data members
  //----------------------------------------------------------------------------

  // current thread's state
  //
  State state;
};

} // namespace ConcuBinE::smtlib

#endif
