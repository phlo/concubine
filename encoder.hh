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
// Encoder base class
//
// Encodes the given Programs into a SMT formula.
//==============================================================================

struct Encoder
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  using ptr = std::unique_ptr<Encoder>;

  // state being updated (to distinguish in Encoder::encode)
  //
  enum class State
    {
      accu,
      mem,
      sb_adr,
      sb_val,
      heap // TODO: really necessary?
    };

  //----------------------------------------------------------------------------
  // static members
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
  // members
  //----------------------------------------------------------------------------

  // reference to the programs being verified (index == thread id)
  //
  // std::shared_ptr - forwarded to the solver for generating a Trace
  //
  Program::List::ptr programs;

  // number of threads (short hand for programs->size())
  //
  size_t num_threads;

  // reference to initial memory layout
  //
  std::shared_ptr<MMap> mmap;

  // bound
  //
  size_t bound;

  // use Sinz's cardinality constraint (num_threads > 4)
  //
  bool use_sinz_constraint;

  // SMT formula buffer
  //
  std::ostringstream formula;

  // current thread id
  //
  word_t thread;

  // current pc
  //
  word_t pc;

  // current state being updated
  //
  State update;

  // pcs of statements requiring an empty store buffer
  //
  // thread -> list of program counters
  //
  std::map<word_t, std::vector<word_t>> flush_pcs; // flushes | require_flush

  // pcs of checkpoint statements
  //
  // checkpoint id -> thread -> list of program counters
  //
  std::map<word_t, std::map<word_t, std::vector<word_t>>> check_pcs; // checkpoints

  // pcs of halt statements
  //
  // thread -> list of program counters
  //
  std::map<word_t, std::vector<word_t>> halt_pcs; // halts

  // pcs of exit calls
  //
  // thread -> list of program counters
  //
  std::map<word_t, std::vector<word_t>> exit_pcs; // exits

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Encoder (const Program::List::ptr & programs,
           const std::shared_ptr<MMap> & mmap,
           size_t bound);

  //----------------------------------------------------------------------------
  // private member functions
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

  // encodes the whole machine configuration
  //
  virtual void encode () = 0;

  // double-dispatched instruction encoding functions (runtime polymorphism)
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

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // returns the SMT formula as string
  //
  // TODO: really necessary?
  //
  std::string str ();

  //----------------------------------------------------------------------------
  // DEBUG
  //
  // TODO: remove
  //----------------------------------------------------------------------------

  std::string predecessors_to_string ();
  std::string check_pcs_to_string ();
  std::string exit_pcs_to_string ();
};

namespace smtlib {

//==============================================================================
// SMT-Lib v2.5 Encoder base class
//==============================================================================

struct Encoder : public ConcuBinE::Encoder
{
  //----------------------------------------------------------------------------
  // static members
  //----------------------------------------------------------------------------

  // bitvector sort declaration
  //
  static const std::string bv_sort;

  // exit code variable
  //
  static const std::string & exit_code_var;

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
  // members
  //----------------------------------------------------------------------------

  // current step
  //
  size_t step;

  // previous step (reduce subtractions)
  //
  size_t prev;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Encoder (const Program::List::ptr & programs,
           const std::shared_ptr<MMap> & mmap,
           size_t bound);

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // thread state variable name generators
  //
  static std::string accu_var (word_t step, word_t thread);
         std::string accu_var () const;
  static std::string mem_var (word_t step, word_t thread);
         std::string mem_var () const;
  static std::string sb_adr_var (word_t step, word_t thread);
         std::string sb_adr_var () const;
  static std::string sb_val_var (word_t step, word_t thread);
         std::string sb_val_var () const;
  static std::string sb_full_var (word_t step, word_t thread);
         std::string sb_full_var () const;
  static std::string stmt_var (word_t step, word_t thread, word_t pc);
         std::string stmt_var () const;
  static std::string block_var (word_t step, word_t thread, word_t id);
  static std::string halt_var (word_t step, word_t thread);
         std::string halt_var () const;

  // machine state variable name generators
  //
  static std::string heap_var (word_t step);
         std::string heap_var () const;
  static std::string exit_flag_var (word_t step);
         std::string exit_flag_var () const;

  // transition variable name generators
  //
  static std::string thread_var (word_t step, word_t thread);
         std::string thread_var () const;
  static std::string exec_var (word_t step, word_t thread, word_t pc);
         std::string exec_var () const;
  static std::string flush_var (word_t step, word_t thread);
         std::string flush_var () const;
  static std::string check_var (word_t step, word_t id);

  // assignment expression generator
  //
  std::string assign (const std::string & variable,
                      const std::string & expression) const;

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

  // state variable definitions
  //
  virtual void define_states () = 0;

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

  // main encoding function
  //
  virtual void encode ();

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
};

//==============================================================================
// SMT-Lib v2.5 Functional Encoder class
//==============================================================================

struct Functional : public Encoder
{
  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  using Encoder::Encoder;

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // state variable definitions
  //
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

  virtual void define_states (); // all of the above

  // main encoding function
  //
  virtual void encode ();

  // double-dispatched instruction encoding functions
  //
  using Encoder::encode;
};

//==============================================================================
// SMT-Lib v2.5 Relational Encoder class
//==============================================================================

struct Relational : public Encoder
{
  //----------------------------------------------------------------------------
  // member types
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
  // members
  //----------------------------------------------------------------------------

  // current step's default states
  //
  State state;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  using Encoder::Encoder;

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

  // state variable definitions
  //
  void imply_thread_executed ();
  void imply_thread_not_executed ();
  void imply_thread_flushed ();
  void imply_machine_exited ();

  virtual void define_states (); // all of the above

  // double-dispatched instruction encoding functions
  //
  using Encoder::encode; // use base class' main encoding function

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
};

} // namespace smtlib

namespace btor2 {

//==============================================================================
// BTOR2 Encoder class
//==============================================================================

struct Encoder : public ConcuBinE::Encoder
{
  //----------------------------------------------------------------------------
  // member types
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
  // static members
  //----------------------------------------------------------------------------

  // exit code variable
  //
  static const std::string & exit_code_var;

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
  // members
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

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Encoder (const Program::List::ptr & programs,
           const std::shared_ptr<MMap> & mmap,
           size_t bound);

  //----------------------------------------------------------------------------
  // private member functions
  //----------------------------------------------------------------------------

  // thread state symbol generators
  //
  static std::string accu_var (word_t thread);
         std::string accu_var () const;
  static std::string mem_var (word_t thread);
         std::string mem_var () const;
  static std::string sb_adr_var (word_t thread);
         std::string sb_adr_var () const;
  static std::string sb_val_var (word_t thread);
         std::string sb_val_var () const;
  static std::string sb_full_var (word_t thread);
         std::string sb_full_var () const;
  static std::string stmt_var (word_t thread, word_t pc);
         std::string stmt_var () const;
  static std::string block_var (word_t thread, word_t id);
  static std::string halt_var (word_t thread);
         std::string halt_var () const;

  // transition symbol generators
  //
  static std::string thread_var (word_t thread);
         std::string thread_var () const;
  static std::string flush_var (word_t thread);
         std::string flush_var () const;
  static std::string exec_var (const word_t t, const word_t pc);
         std::string exec_var () const;
  static std::string check_var (word_t id);

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

  // main encoding function
  //
  virtual void encode ();

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
};

} // namespace btor2
} // namespace ConcuBinE

#endif
