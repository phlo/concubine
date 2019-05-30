#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <functional>
#include <sstream>
#include <map>
#include <set>
#include <vector>

#include "instructionset.hh"
#include "program.hh"

/*******************************************************************************
 * Encodes the given Programs into a SMT formula.
 ******************************************************************************/
struct Encoder
{
  /* constructs an Encoder for the given program and bound */
  Encoder (const Program_list_ptr programs, unsigned long bound);

  /* reference to the programs being verified (index == thread id) */
  const Program_list_ptr  programs;

  /* number of threads (short hand for programs->size()) */
  const unsigned long     num_threads;

  /* bound */
  const unsigned long     bound;

  /* use Sinz's cardinality constraint (num_threads > 4) */
  const bool              use_sinz_constraint;

  /* SMT formula */
  std::ostringstream      formula;

  /* current thread id */
  word_t                  thread;

  /* current pc */
  word_t                  pc;

  /* pcs of predecessor for each statement */
  std::map<
    word_t,
    std::map<
      word_t,
      std::set<word_t>>>  predecessors;

  /* pcs of checkpoint statements (checkpoint id -> thread -> pc) */
  std::map<
    word_t,
    std::map<
      word_t,
      std::set<word_t>>>  check_pcs;

  /* pcs of exit calls */
  std::unordered_map<
    word_t,
    std::vector<word_t>>  exit_pcs;

  /* threads containing CAS statements */
  // TODO: really necessary?
  std::set<word_t>        cas_threads;

  /*****************************************************************************
   * private functions
  *****************************************************************************/
  void iterate_threads (std::function<void()>);
  void iterate_threads (std::function<void(Program &)>);
  void iterate_threads_reverse (std::function<void(Program &)>);

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

  /* print the SMT formula to stdout */
  void                print ();

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
 * EncoderPtr
 ******************************************************************************/
typedef std::shared_ptr<Encoder> EncoderPtr;

/*******************************************************************************
 * SMT-Lib v2.5 Encoder Base Class
 ******************************************************************************/
struct SMTLibEncoder : public Encoder
{
  /* constructs an SMTLibEncoder for the given program and bound */
  SMTLibEncoder (const Program_list_ptr programs, unsigned long bound);

  /* encoder variables */
  unsigned long             step;

  /* string nids_const */
  static const std::string  bv_sort;

  static const std::string  exit_code_var;

  /* variable comments */
  static const std::string  heap_comment;
  static const std::string  accu_comment;
  static const std::string  mem_comment;

  static const std::string  stmt_comment;
  static const std::string  thread_comment;
  static const std::string  exec_comment;
  static const std::string  cas_comment;
  static const std::string  block_comment;
  static const std::string  check_comment;
  static const std::string  exit_comment;

  /* state variable generators */
  std::string               heap_var (const word_t);
  std::string               heap_var ();
  std::string               accu_var (const word_t, const word_t);
  std::string               accu_var ();
  std::string               mem_var (const word_t, const word_t);
  std::string               mem_var ();

  /* transition variable generators */
  std::string               stmt_var (const word_t, const word_t, const word_t);
  std::string               stmt_var ();
  std::string               thread_var (const word_t, const word_t);
  std::string               thread_var ();
  std::string               exec_var (const word_t, const word_t, const word_t);
  std::string               exec_var ();
  std::string               cas_var (const word_t, const word_t);
  std::string               cas_var ();
  std::string               block_var (const word_t, const word_t, const word_t);
  std::string               check_var (const word_t, const word_t);
  std::string               exit_var (const word_t);
  std::string               exit_var ();

  /* variable declaration generators */
  void                      declare_heap_var ();
  void                      declare_accu_vars ();
  void                      declare_mem_vars ();

  void                      declare_stmt_vars ();
  void                      declare_thread_vars ();
  void                      declare_exec_vars ();
  void                      declare_cas_vars ();
  void                      declare_block_vars ();
  void                      declare_check_vars ();
  void                      declare_exit_var ();
  void                      declare_exit_code ();

  /* expression generators */
  std::string               assign_var (std::string, std::string);

  /* common encodings */
  void                      add_initial_state ();
  void                      add_initial_statement_activation ();

  void                      add_exit_flag ();
  void                      add_thread_scheduling ();
  void                      add_checkpoint_constraints ();
  void                      add_statement_execution ();

  std::string               load(Load &);

  virtual void              encode ();
};

/*******************************************************************************
 * SMTLibEncoderPtr
 ******************************************************************************/
typedef std::shared_ptr<SMTLibEncoder> SMTLibEncoderPtr;

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
struct SMTLibEncoderFunctional : public SMTLibEncoder
{
  /* constructs an SMTLibEncoderFunctional for the given program and bound */
  SMTLibEncoderFunctional (
                           const Program_list_ptr programs,
                           unsigned long bound,
                           bool encode = true
                          );

  /* accumulator altering pcs */
  std::unordered_map<word_t, std::vector<word_t>> alters_accu;

  /* CAS memory register altering pcs */
  std::unordered_map<word_t, std::vector<word_t>> alters_mem;

  /* heap altering pcs */
  std::unordered_map<word_t, std::vector<word_t>> alters_heap;

  /* flag to distinguish between accu and heap updates when encoding CAS */
  bool                update_accu;

  void                add_statement_activation ();
  void                add_state_update ();
  void                add_exit_code ();

  /* encodes the whole machine configuration */
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
 * SMTLibEncoderFunctionalPtr
 ******************************************************************************/
typedef std::shared_ptr<SMTLibEncoderFunctional> SMTLibEncoderFunctionalPtr;

/*******************************************************************************
 * SMT-Lib v2.5 Relational Encoder Class
 ******************************************************************************/
struct SMTLibEncoderRelational : public SMTLibEncoder
{
  /* constructs an SMTLibEncoderRelational for the given program and bound */
  SMTLibEncoderRelational (
                           const Program_list_ptr programs,
                           unsigned long bound,
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

  void                add_exit_code ();
  void                add_statement_declaration ();
  void                add_state_update ();
  void                add_state_preservation ();

  /* encodes the whole machine configuration */
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
 * SMTLibEncoderRelationalPtr
 ******************************************************************************/
typedef std::shared_ptr<SMTLibEncoderRelational> SMTLibEncoderRelationalPtr;

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
                unsigned long bound,
                bool encode = true
               );

  /* accumulator altering pcs */
  std::unordered_map<word_t, std::vector<word_t>> alters_accu;

  /* CAS memory register altering pcs */
  std::unordered_map<word_t, std::vector<word_t>> alters_mem;

  /* heap altering pcs */
  std::unordered_map<word_t, std::vector<word_t>> alters_heap;

  /* flag to distinguish between accu and heap updates when encoding CAS */
  bool                          update_accu;

  /* next node id */
  unsigned long                 node;

  std::string                   sid_bool,
                                sid_bv,
                                sid_heap,

                                nid_true,
                                nid_false,

                                nid_heap,

                                nid_exit,
                                nid_exit_code;

  std::map<word_t, std::string> nids_const,

                                nids_accu,
                                nids_mem,

                                nids_thread,
                                nids_check,

                                nids_load,
                                nids_load_indirect;

  std::map<
    word_t,
    std::vector<std::string>>   nids_stmt,
                                nids_exec;

  std::map<
    word_t,
    std::map<
      word_t,
      std::string>>             nids_block,
                                nids_store,
                                nids_store_indirect;

  std::string                   nid ();
  std::string                   nid (int offset);

  std::string                   symbol (word_t pc);

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
                                              std::unordered_map<
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

  /* encodes the whole machine configuration */
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
 * Btor2EncoderPtr
 ******************************************************************************/
typedef std::shared_ptr<Btor2Encoder> Btor2EncoderPtr;

#endif
