#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <map>
#include <set>
#include <sstream>
#include <vector>

#include "instructionset.hh"
#include "program.hh"

/*******************************************************************************
 * Encodes the given Programs into a SMT formula.
 ******************************************************************************/
struct Encoder
{
  // TODO: change back to using {unordered_}{map,set} directly
  template <class K, class V>
  using Map = std::unordered_map<K, V>;

  template <class V>
  using Set = std::unordered_set<V>;

  using Type = Instruction::Type;
  using Types = Instruction::Types;

  /* thread state symbols */
  static const std::string accu_sym;
  static const std::string mem_sym;
  static const std::string sb_adr_sym;
  static const std::string sb_val_sym;
  static const std::string sb_full_sym;
  static const std::string stmt_sym;
  static const std::string block_sym;

  /* machine state symbols */
  static const std::string heap_sym;
  static const std::string exit_sym;
  static const std::string exit_code_sym;

  /* transition symbols */
  static const std::string thread_sym;
  static const std::string flush_sym;
  static const std::string check_sym;
  static const std::string exec_sym;
  static const std::string cas_sym; // TODO: really needed?

  /* reference to the programs being verified (index == thread id) */
  const Program_list_ptr  programs;

  /* number of threads (short hand for programs->size()) */
  const size_t            num_threads;

  /* bound */
  const bound_t           bound;

  /* use Sinz's cardinality constraint (num_threads > 4) */
  const bool              use_sinz_constraint;

  /* SMT formula */
  std::ostringstream      formula;

  /* current thread id */
  word_t                  thread;

  /* current pc */
  word_t                  pc;

  /* state being updated (for being able to distinguish in Encoder::encode) */
  enum class Update
    {
      accu,
      mem,
      sb_adr,
      sb_val,
      heap // TODO: really necessary?
    };

  Update update;

  /* pcs of statements requiring an empty store buffer */
  Map<
    word_t,
    std::set<word_t>>     flush_pcs;

  /* pcs of checkpoint statements (checkpoint id -> thread -> pc) */
  std::map<
    word_t,
    std::map<
      word_t,
      std::set<word_t>>>  check_pcs;

  /* pcs of exit calls */
  Map<
    word_t,
    std::vector<word_t>>  exit_pcs;

  /* threads containing CAS statements */
  // TODO: really necessary?
  Set<word_t>             cas_threads;

  /* constructs an Encoder for the given program and bound */
  Encoder (const Program_list_ptr programs, bound_t bound);

  /*****************************************************************************
   * private functions
  *****************************************************************************/
  template<class Functor>
  void iterate_threads (const Functor fun)
    {
      for (thread = 0; thread < num_threads; thread++)
        fun();
    }

  template<class Functor>
  void iterate_programs (const Functor fun)
    {
      thread = 0;
      for (const Program_ptr & program : *programs)
        {
          fun(*program);
          thread++;
        }
    }

  template<class Functor>
  void iterate_programs_reverse (const Functor fun)
    {
      thread = num_threads - 1;
      for (auto rit = programs->rbegin(); rit != programs->rend(); ++rit)
        {
          fun(**rit);
          thread--;
        }
    }

  /* double-dispatched instruction encoding functions */
  virtual std::string encode (Load &) = 0;
  virtual std::string encode (Store &) = 0;

  virtual std::string encode (Fence &) = 0;

  virtual std::string encode (Add &) = 0;
  virtual std::string encode (Addi &) = 0;
  virtual std::string encode (Sub &) = 0;
  virtual std::string encode (Subi &) = 0;

  virtual std::string encode (Cmp &) = 0;
  virtual std::string encode (Jmp &) = 0;
  virtual std::string encode (Jz &) = 0;
  virtual std::string encode (Jnz &) = 0;
  virtual std::string encode (Js &) = 0;
  virtual std::string encode (Jns &) = 0;
  virtual std::string encode (Jnzns &) = 0;

  virtual std::string encode (Mem &) = 0;
  virtual std::string encode (Cas &) = 0;

  virtual std::string encode (Check &) = 0;

  virtual std::string encode (Halt &) = 0;
  virtual std::string encode (Exit &) = 0;

  /*****************************************************************************
   * public functions
  *****************************************************************************/

  /* encodes the whole machine configuration */
  virtual void        encode () = 0;

  /* returns the SMT formula as string */
  std::string         str ();

  /*****************************************************************************
   * DEBUG
  *****************************************************************************/
  std::string predecessors_to_string ();
  std::string check_pcs_to_string ();
  std::string exit_pcs_to_string ();
};

/*******************************************************************************
 * Encoder_ptr
 ******************************************************************************/
using Encoder_ptr = std::shared_ptr<Encoder>;

/*******************************************************************************
 * SMT-Lib v2.5 Encoder Base Class
 ******************************************************************************/
struct SMTLibEncoder : public Encoder
{
  /* constructs an SMTLibEncoder for the given program and bound */
  SMTLibEncoder (const Program_list_ptr programs, bound_t bound);

  /* encoder variables */
  bound_t                   step,
                            prev;

  static const std::string  bv_sort;

  static const std::string  exit_code_var;

  /* variable comments */
  static const std::string  accu_comment;
  static const std::string  mem_comment;
  static const std::string  sb_adr_comment;
  static const std::string  sb_val_comment;
  static const std::string  sb_full_comment;
  static const std::string  stmt_comment;
  static const std::string  block_comment;

  static const std::string  exit_comment;
  static const std::string  heap_comment;

  static const std::string  thread_comment;
  static const std::string  flush_comment;
  static const std::string  check_comment;
  static const std::string  exec_comment;
  static const std::string  cas_comment;

  /* thread state variable generators */
  static std::string        accu_var (const word_t k, const word_t t);
  std::string               accu_var () const;
  static std::string        mem_var (const word_t k, const word_t t);
  std::string               mem_var () const;
  static std::string        sb_adr_var (const word_t k, const word_t t);
  std::string               sb_adr_var () const;
  static std::string        sb_val_var (const word_t k, const word_t t);
  std::string               sb_val_var () const;
  static std::string        sb_full_var (const word_t k, const word_t t);
  std::string               sb_full_var () const;
  static std::string        stmt_var (
                                      const word_t k,
                                      const word_t t,
                                      const word_t pc
                                     );
  std::string               stmt_var () const;
  static std::string        block_var (
                                       const word_t k,
                                       const word_t t,
                                       const word_t id
                                      );

  /* machine state variable generators */
  static std::string        heap_var (const word_t k);
  std::string               heap_var () const;
  static std::string        exit_var (const word_t k);
  std::string               exit_var () const;

  /* transition variable name generators */
  static std::string        thread_var (const word_t k, const word_t t);
  std::string               thread_var () const;
  static std::string        flush_var (const word_t k, const word_t t);
  std::string               flush_var () const;
  static std::string        check_var (const word_t k, const word_t id);
  static std::string        exec_var (
                                      const word_t k,
                                      const word_t t,
                                      const word_t pc
                                     );
  std::string               exec_var () const;

  /*
  static std::string        cas_var (const word_t k, const word_t t);
  std::string               cas_var () const;
  */

  /* expression generators */
  std::string               assign_var (std::string, std::string);
  std::string               load(word_t address, bool indirect = false);

  /* state variable declarations */
  void                      declare_accu ();
  void                      declare_mem ();
  void                      declare_sb_adr ();
  void                      declare_sb_val ();
  void                      declare_sb_full ();
  void                      declare_stmt ();
  void                      declare_block ();

  void                      declare_heap ();
  void                      declare_exit ();
  void                      declare_exit_code ();

  void                      declare_states ();

  /* transition variable declarations */
  void                      declare_thread ();
  void                      declare_flush ();
  void                      declare_check ();
  void                      declare_exec ();
  // void                      declare_cas ();

  void                      declare_transitions ();

  /* state variable definitions */
  virtual void              define_states () = 0;

  /* transition variable definitions */
  void                      define_check ();
  void                      define_exec ();
  // void                      define_cas ();

  void                      define_transitions ();

  /* constraint definitions */
  void                      define_store_buffer_constraints ();
  void                      define_checkpoint_contraints ();
  void                      define_scheduling_constraints ();
  void                      define_constraints ();

  /* main encoding function */
  virtual void              encode ();
};

/*******************************************************************************
 * SMTLibEncoder_ptr
 ******************************************************************************/
using SMTLibEncoder_ptr = std::shared_ptr<SMTLibEncoder>;

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
struct SMTLibEncoderFunctional : public SMTLibEncoder
{
  /* constructs an SMTLibEncoderFunctional for the given program and bound */
  SMTLibEncoderFunctional (
                           const Program_list_ptr programs,
                           bound_t bound,
                           bool encode = true
                          );

  /* thread state definitions */
  void                define_accu ();
  void                define_mem ();
  void                define_sb_adr ();
  void                define_sb_val ();
  void                define_sb_full ();
  void                define_stmt ();
  void                define_block ();

  /* machine state definitions */
  void                define_heap ();
  void                define_exit ();
  void                define_exit_code ();

  virtual void        define_states ();

  /* main encoding function */
  virtual void        encode ();

  /* double-dispatched instruction encoding functions */
  virtual std::string encode (Load &);
  virtual std::string encode (Store &);

  virtual std::string encode (Fence &);

  virtual std::string encode (Add &);
  virtual std::string encode (Addi &);
  virtual std::string encode (Sub &);
  virtual std::string encode (Subi &);

  virtual std::string encode (Cmp &);
  virtual std::string encode (Jmp &);
  virtual std::string encode (Jz &);
  virtual std::string encode (Jnz &);
  virtual std::string encode (Js &);
  virtual std::string encode (Jns &);
  virtual std::string encode (Jnzns &);

  virtual std::string encode (Mem &);
  virtual std::string encode (Cas &);

  virtual std::string encode (Check &);

  virtual std::string encode (Halt &);
  virtual std::string encode (Exit &);
};

/*******************************************************************************
 * SMTLibEncoderFunctional_ptr
 ******************************************************************************/
using SMTLibEncoderFunctional_ptr = std::shared_ptr<SMTLibEncoderFunctional>;

/*******************************************************************************
 * SMT-Lib v2.5 Relational Encoder Class
 ******************************************************************************/
struct SMTLibEncoderRelational : public SMTLibEncoder
{
  /* constructs an SMTLibEncoderRelational for the given program and bound */
  SMTLibEncoderRelational (
                           const Program_list_ptr programs,
                           bound_t bound,
                           bool encode = true
                          );

  std::string         imply (std::string, std::string);

  std::string         assign_heap (std::string);
  std::string         assign_accu (std::string);
  std::string         assign_mem (std::string);

  std::string         preserve_heap ();
  std::string         preserve_accu ();
  std::string         preserve_mem ();

  std::string         stmt_activation (word_t);

  std::string         activate_pc (word_t);
  std::string         activate_next ();
  std::string         activate_jmp (std::string, word_t);

  /*
  void                add_exit_code ();
  void                add_statement_declaration ();
  void                add_state_updates ();
  void                add_state_preservation ();
  */

  /* state variable definitions */
  virtual void        define_states ();

  /* double-dispatched instruction encoding functions */
  using SMTLibEncoder::encode;

  virtual std::string encode (Load &);
  virtual std::string encode (Store &);

  virtual std::string encode (Fence &);

  virtual std::string encode (Add &);
  virtual std::string encode (Addi &);
  virtual std::string encode (Sub &);
  virtual std::string encode (Subi &);

  virtual std::string encode (Cmp &);
  virtual std::string encode (Jmp &);
  virtual std::string encode (Jz &);
  virtual std::string encode (Jnz &);
  virtual std::string encode (Js &);
  virtual std::string encode (Jns &);
  virtual std::string encode (Jnzns &);

  virtual std::string encode (Mem &);
  virtual std::string encode (Cas &);

  virtual std::string encode (Check &);

  virtual std::string encode (Halt &);
  virtual std::string encode (Exit &);
};

/*******************************************************************************
 * SMTLibEncoderRelational_ptr
 ******************************************************************************/
using SMTLibEncoderRelational_ptr = std::shared_ptr<SMTLibEncoderRelational>;

/*******************************************************************************
 * Btor2 Encoder Class
 ******************************************************************************/
struct Btor2Encoder : public Encoder
{
  /* most significant bit */
  static std::string          msb;

  /* constructs a Btor2Encoder for the given program and bound */
  Btor2Encoder (
                const Program_list_ptr programs,
                bound_t bound,
                bool encode = true
               );

  /* accumulator altering pcs */
  Map<word_t, std::vector<word_t>> alters_accu;

  /* CAS memory register altering pcs */
  Map<word_t, std::vector<word_t>> alters_mem;

  /* heap altering pcs */
  Map<word_t, std::vector<word_t>> alters_heap;

  /* flag to distinguish between accu and heap updates when encoding CAS */
  bool                          update_accu;

  /* next node id */
  uint64_t                      node;

  std::string                   sid_bool,
                                sid_bv,
                                sid_heap,

                                nid_true,
                                nid_false,

                                nid_heap,

                                nid_exit,
                                nid_exit_code;

  Map<word_t, std::string>      nids_const,

                                nids_accu,
                                nids_mem,

                                nids_thread,
                                nids_check,

                                nids_load,
                                nids_load_indirect;

  Map<
    word_t,
    std::vector<std::string>>   nids_stmt,
                                nids_exec;

  Map<
    word_t,
    Map<
      word_t,
      std::string>>             nids_block,
                                nids_store,
                                nids_store_indirect;

  std::string                   nid ();
  std::string                   nid (int offset);

  std::string                   debug_symbol (word_t pc);

  static std::string            accu_var (const word_t t);
  std::string                   accu_var () const;
  static std::string            mem_var (const word_t t);
  std::string                   mem_var () const;

  static std::string            stmt_var (const word_t t, const word_t pc);
  std::string                   stmt_var () const;
  static std::string            thread_var (const word_t t);
  std::string                   thread_var () const;
  static std::string            exec_var (const word_t t, const word_t pc);
  std::string                   exec_var () const;
  static std::string            cas_var (const word_t t); // TODO: remove (unused)
  std::string                   cas_var () const; // TODO: remove (unused)
  static std::string            block_var (const word_t t, const word_t id);
  static std::string            check_var (const word_t id);

  void                          declare_heap ();
  void                          declare_accu ();
  void                          declare_mem ();
  void                          declare_stmt ();
  void                          declare_block ();
  void                          declare_exit_flag ();
  void                          declare_exit_code ();

  void                          define_state (
                                              std::string nid,
                                              std::string sid,
                                              std::string nid_init,
                                              std::string symbol,
                                              Map<
                                                word_t,
                                                std::vector<word_t>> & alters,
                                              const bool global = false
                                             );
  void                          define_accu ();
  void                          define_mem ();
  void                          define_heap ();
  void                          define_stmt ();
  void                          define_block ();
  void                          define_check ();
  void                          define_exit_flag ();
  void                          define_exit_code ();

  void                          add_sorts ();
  void                          add_constants ();
  void                          add_machine_state_declarations ();
  void                          add_thread_scheduling ();
  void                          add_statement_execution ();
  void                          add_statement_activation ();
  void                          add_register_definitions ();
  void                          add_heap_definition ();
  void                          add_exit_definitions ();
  void                          add_checkpoint_constraints ();
  void                          add_bound ();

  std::string                   add_load(std::string *);

  std::string                   load(Load & l);
  std::string                   store(Store & s);

  /* main encoding function */
  virtual void                  encode ();

  /* double-dispatched instruction encoding functions */
  virtual std::string           encode (Load &);
  virtual std::string           encode (Store &);

  virtual std::string           encode (Fence &);

  virtual std::string           encode (Add &);
  virtual std::string           encode (Addi &);
  virtual std::string           encode (Sub &);
  virtual std::string           encode (Subi &);

  virtual std::string           encode (Cmp &);
  virtual std::string           encode (Jmp &);
  virtual std::string           encode (Jz &);
  virtual std::string           encode (Jnz &);
  virtual std::string           encode (Js &);
  virtual std::string           encode (Jns &);
  virtual std::string           encode (Jnzns &);

  virtual std::string           encode (Mem &);
  virtual std::string           encode (Cas &);

  virtual std::string           encode (Check &);

  virtual std::string           encode (Halt &);
  virtual std::string           encode (Exit &);
};

/*******************************************************************************
 * Btor2Encoder_ptr
 ******************************************************************************/
using Btor2Encoder_ptr = std::shared_ptr<Btor2Encoder>;

#endif
