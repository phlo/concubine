#ifndef ENCODER_BTOR2_HH_
#define ENCODER_BTOR2_HH_

#include "encoder.hh"

namespace ConcuBinE::btor2 {

//==============================================================================
// BTOR2 Encoder
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

  // static thread state variable name generators
  //
  static std::string accu_var (word_t thread);
  static std::string mem_var (word_t thread);
  static std::string sb_adr_var (word_t thread);
  static std::string sb_val_var (word_t thread);
  static std::string sb_full_var (word_t thread);
  static std::string stmt_var (word_t thread, word_t pc);
  static std::string block_var (word_t thread, word_t id);
  static std::string halt_var (word_t thread);

  // static transition variable name generators
  //
  static std::string thread_var (word_t thread);
  static std::string flush_var (word_t thread);
  static std::string exec_var (const word_t t, const word_t pc);
  static std::string check_var (word_t id);

  //----------------------------------------------------------------------------
  // public member functions inherited from ConcuBinE::Encoder
  //----------------------------------------------------------------------------

  // main encoding function
  //
  virtual void encode ();

  // add exit code assertion
  //
  virtual void assert_exit ();

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private member types
  //----------------------------------------------------------------------------

  // node id
  //
  using nid_t = uint64_t;

  // list of node ids
  //
  using nid_list = std::vector<std::string>;

  // map of unsigned integers to node ids
  //
  using nid_map = std::unordered_map<word_t, std::string>;

  //----------------------------------------------------------------------------
  // private constants
  //----------------------------------------------------------------------------

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

  // most significant bit's bitvector constant
  //
  static const std::string msb;

  //----------------------------------------------------------------------------
  // private member functions
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

  // transition variable name generators
  //
  std::string thread_var () const;
  std::string flush_var () const;
  std::string exec_var () const;

  // get and advance current nid
  //
  std::string nid ();
  std::string nid (int offset);

  // debug symbol generator ("thread:pc:symbol:arg")
  std::string debug_symbol (word_t thread, word_t pc);

  // load expression generator
  //
  std::string load (word_t address, bool indirect = false);

  // sort declarations
  //
  void declare_sorts ();

  // constant declarations
  //
  void declare_constants ();

  // memory map definition
  //
  void define_mmap ();

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

  // input variable declarations
  //
  void declare_thread ();
  void declare_flush ();

  void declare_inputs (); // all of the above

  // transition variable definitions
  //
  void define_exec ();
  void define_check ();

  void define_transitions (); // all of the above

  // state variable definitions
  //
  void define_state_bv (Instruction::Type type,
                        const std::string & nid,
                        std::string symbol);

  void define_accu ();
  void define_mem ();
  void define_sb_adr ();
  void define_sb_val ();
  void define_sb_full ();
  void define_stmt ();
  void define_block ();
  void define_halt ();

  void define_heap ();
  void define_exit_flag ();
  void define_exit_code ();

  void define_states (); // all of the above

  // constraint definitions
  //
  void define_scheduling_constraints ();
  void define_store_buffer_constraints ();
  void define_checkpoint_constraints ();
  void define_halt_constraints ();

  void define_constraints (); // all of the above

  // bound (only used in random "simulation")
  //
  void define_bound ();

  //----------------------------------------------------------------------------
  // private member functions inherited from ConcuBinE::Encoder
  //----------------------------------------------------------------------------

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

  // current node id
  //
  nid_t node;

  // sorts
  //
  std::string sid_bool;
  std::string sid_bv;
  std::string sid_heap;

  // boolean constants
  //
  std::string nid_true;
  std::string nid_false;

  // bitvector constants
  //
  // constant -> nid
  //
  std::map<word_t, std::string> nids_const;

  // memory map state node used in heap initialization
  //
  std::string nid_mmap;

  // register state nodes
  //
  // thread -> nid
  //
  nid_list nids_accu;
  nid_list nids_mem;

  nid_list nids_sb_adr;
  nid_list nids_sb_val;
  nid_list nids_sb_full;

  // statement activation state nodes
  //
  // thread -> pc -> nid
  //
  std::vector<nid_list> nids_stmt;

  // blocking state nodes
  //
  // checkpoint id -> thread -> nid
  //
  std::map<word_t, std::map<word_t, std::string>> nids_block;

  // halt state nodes
  //
  // thread -> nid
  //
  std::map<word_t, std::string> nids_halt;

  // halt state definition nodes (as used in next)
  //
  // required in exit_flag definition: exit_flag and last halt set in same step
  //
  std::map<word_t, std::string> nids_halt_next;

  // machine state nodes
  //
  std::string nid_heap;

  std::string nid_exit_flag;
  std::string nid_exit_code;

  // thread input nodes
  //
  // thread -> nid
  //
  nid_list nids_thread;

  // execution variable nodes
  //
  // thread -> pc -> nid
  //
  std::vector<nid_list> nids_exec;

  // flush input nodes
  //
  // thread -> nid
  //
  nid_list nids_flush;

  // checkpoint variable nodes
  //
  // checkpoint id -> nid
  //
  std::map<word_t, std::string> nids_check;

  // array read nodes
  //
  // address -> nid
  //
  nid_map nids_read;
  nid_map nids_read_indirect;

  // store buffer contains address condition nodes
  //
  // thread -> address -> nid
  //
  std::unordered_map<word_t, nid_map> nids_eq_sb_adr_adr;

  // indirect load expression using store buffer value (heap[sb-val]) nodes
  //
  // thread -> nid
  //
  nid_map nids_read_sb_val;

  // load expression nodes
  //
  // thread -> address -> nid
  //
  std::unordered_map<word_t, nid_map> nids_load;
  std::unordered_map<word_t, nid_map> nids_load_indirect;

  // CAS condition nodes: thread -> address -> nid
  std::unordered_map<word_t, nid_map> nids_cas;
  std::unordered_map<word_t, nid_map> nids_cas_indirect;
};

} // namespace ConcuBinE::btor2

#endif
