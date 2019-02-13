#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <functional>
#include <sstream>
#include <map>
#include <set>
#include <vector>

#include "program.hh"

/*******************************************************************************
 * Encodes the given Programs into a SMT formula.
 ******************************************************************************/
struct Encoder
{
  /* constructs an Encoder for the given program and bound */
  Encoder (const ProgramListPtr, unsigned long);

  /* reference to the programs being verified (index == thread id) */
  const ProgramListPtr  programs;

  /* number of threads (short hand for programs->size()) */
  const unsigned long   num_threads;

  /* bound */
  const unsigned long   bound;

  /* use Sinz's cardinality constraint (num_threads > 4) */
  const bool            use_sinz_constraint;

  /* SMT formula */
  std::ostringstream    formula;

  /* current thread id */
  word                  thread;

  /* current pc */
  word                  pc;

  /* pcs of predecessor for each statement */
  std::map<
    word,
    std::map<
      word,
      std::set<word>>>  predecessors;

  /* pcs of sync statements (sync id -> thread -> pc) */
  std::map<
    word,
    std::map<
      word,
      std::set<word>>>  sync_pcs;

  /* pcs of exit calls */
  std::map<word, std::set<word>> exit_pcs;

  /* threads containing CAS statements */
  std::set<word>        cas_threads;

  /*****************************************************************************
   * private functions
  *****************************************************************************/

  void                iterate_threads (std::function<void(void)>);
  void                iterate_threads (std::function<void(Program &)>);
  void                iterate_threads_reverse (std::function<void(Program &)>);

  /* double-dispatched instruction encoding functions */
  virtual std::string encode (Load &) = 0;
  virtual std::string encode (Store &) = 0;

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

  virtual std::string encode (Sync &) = 0;
  virtual std::string encode (Exit &) = 0;

  /* initialize internal data structures */
  virtual void        preprocess (void);

  /*****************************************************************************
   * public functions
  *****************************************************************************/

  /* encodes the whole machine configuration */
  virtual void        encode (void) = 0;

  /* print the SMT formula to stdout */
  void                print (void);

  /* returns the SMT formula as string */
  std::string         str (void);

  /*****************************************************************************
   * DEBUG
  *****************************************************************************/
  std::string         predecessors_to_string (void);
  std::string         sync_pcs_to_string (void);
  std::string         exit_pcs_to_string (void);
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
  SMTLibEncoder (const ProgramListPtr, unsigned long);

  /* encoder variables */
  unsigned long             step;

  /* string constants */
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
  static const std::string  sync_comment;
  static const std::string  exit_comment;

  /* state variable generators */
  std::string               heap_var (const word);
  std::string               heap_var (void);
  std::string               accu_var (const word, const word);
  std::string               accu_var (void);
  std::string               mem_var (const word, const word);
  std::string               mem_var (void);

  /* transition variable generators */
  std::string               stmt_var (const word, const word, const word);
  std::string               stmt_var (void);
  std::string               thread_var (const word, const word);
  std::string               thread_var (void);
  std::string               exec_var (const word, const word, const word);
  std::string               exec_var (void);
  std::string               cas_var (const word, const word);
  std::string               cas_var (void);
  std::string               sync_var (const word, const word);
  std::string               exit_var (const word);
  std::string               exit_var (void);

  /* variable declaration generators */
  void                      declare_heap_var (void);
  void                      declare_accu_vars (void);
  void                      declare_mem_vars (void);

  void                      declare_stmt_vars (void);
  void                      declare_thread_vars (void);
  void                      declare_exec_vars (void);
  void                      declare_cas_vars (void);
  void                      declare_sync_vars (void);
  void                      declare_exit_var (void);
  void                      declare_exit_code (void);

  /* expression generators */
  std::string               assign_var (std::string, std::string);

  /* common encodings */
  void                      add_initial_state (void);
  void                      add_initial_statement_activation (void);

  void                      add_exit_flag (void);
  void                      add_thread_scheduling (void);
  void                      add_synchronization_constraints (void);
  void                      add_statement_execution (void);

  std::string               load(Load &);

  virtual void              encode (void);
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
  SMTLibEncoderFunctional (const ProgramListPtr, unsigned long, bool = true);

  /* heap altering pcs */
  std::unordered_map<word, std::vector<word>> heap_pcs;

  /* accumulator altering pcs */
  std::unordered_map<word, std::vector<word>> accu_pcs;

  /* CAS memory register altering pcs */
  std::unordered_map<word, std::vector<word>> mem_pcs;

  void                add_statement_activation (void);
  void                add_state_update (void);
  void                add_exit_code (void);

  /* initialize internal data structures */
  virtual void        preprocess (void);

  /* encodes the whole machine configuration */
  virtual void        encode (void);

  /* double-dispatched instruction encoding functions */
  virtual std::string encode (Load &);
  virtual std::string encode (Store &);

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

  virtual std::string encode (Sync &);
  virtual std::string encode (Exit &);
};

/*******************************************************************************
 * SMTLibEncoderFunctionalPtr
 ******************************************************************************/
typedef std::shared_ptr<SMTLibEncoderFunctional> SMTLibEncoderFunctionalPtr;

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
struct SMTLibEncoderRelational : public SMTLibEncoder
{
  /* constructs an SMTLibEncoderRelational for the given program and bound */
  SMTLibEncoderRelational (const ProgramListPtr, unsigned long, bool = true);

  std::string         imply (std::string, std::string);

  std::string         assign_heap (std::string);
  std::string         assign_accu (std::string);
  std::string         assign_mem (std::string);

  std::string         preserve_heap (void);
  std::string         preserve_accu (void);
  std::string         preserve_mem (void);

  std::string         stmt_activation (word);

  std::string         activate_pc (word);
  std::string         activate_next (void);
  std::string         activate_jmp (std::string, word);

  void                add_exit_code (void);
  void                add_statement_declaration (void);
  void                add_state_update (void);
  void                add_state_preservation (void);

  /* encodes the whole machine configuration */
  virtual void        encode (void);

  /* double-dispatched instruction encoding functions */
  virtual std::string encode (Load &);
  virtual std::string encode (Store &);

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

  virtual std::string encode (Sync &);
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
  /* constructs a Btor2Encoder for the given program and bound */
  Btor2Encoder (const ProgramListPtr, unsigned long, bool = true);

  unsigned long               node;

  std::string                 sid_bool,
                              sid_bv,
                              sid_heap,

                              nid_true,
                              nid_false,

                              nid_heap,

                              nid_exit;


  // TODO: rename to nid_constants
  std::map<word, std::string> constants,

                              nid_accu,
                              nid_mem,

                              nid_thread,
                              nid_sync;

  std::map<
    word,
    std::vector<std::string>> nid_stmt,
                              nid_exec;

  std::string                 nid (void);

  void                        declare_sorts (void);
  void                        declare_constants (void);
  void                        declare_states (void);

  void                        add_bound (void);
  void                        add_thread_scheduling (void);
  void                        add_synchronization_constraints (void);
  void                        add_statement_execution (void);

  virtual void                preprocess (void);

  /* encodes the whole machine configuration */
  virtual void                encode (void);

  /* double-dispatched instruction encoding functions */
  virtual std::string         encode (Load &);
  virtual std::string         encode (Store &);

  virtual std::string         encode (Add &);
  virtual std::string         encode (Addi &);
  virtual std::string         encode (Sub &);
  virtual std::string         encode (Subi &);

  virtual std::string         encode (Cmp &);
  virtual std::string         encode (Jmp &);
  virtual std::string         encode (Jz &);
  virtual std::string         encode (Jnz &);
  virtual std::string         encode (Js &);
  virtual std::string         encode (Jns &);
  virtual std::string         encode (Jnzns &);

  virtual std::string         encode (Mem &);
  virtual std::string         encode (Cas &);

  virtual std::string         encode (Sync &);
  virtual std::string         encode (Exit &);
};

/*******************************************************************************
 * Btor2EncoderPtr
 ******************************************************************************/
typedef std::shared_ptr<Btor2Encoder> Btor2EncoderPtr;

#endif
