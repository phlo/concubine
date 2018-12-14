#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <functional>
#include <sstream>
#include <map>
#include <set>

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

  /* pcs of sync statements (per id) */
  std::map<
    word,
    std::map<
      word,
      std::set<word>>>  sync_pcs;

  /*****************************************************************************
   * private functions
  *****************************************************************************/

  void                      iterate_threads (std::function<void(void)>);
  void                      iterate_threads (std::function<void(ProgramPtr)>);

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

  /* collects jump targets used in the current program */
  void                collect_predecessors (void);

  /* initialize internal data structures */
  void                preprocess (void);

  /*****************************************************************************
   * public functions
  *****************************************************************************/

  /* encodes the whole machine configuration */
  virtual void        encode (void) = 0;

  /* print the SMT formula to stdout */
  void                print (void);

  /* returns the SMT formula as string */
  std::string         to_string (void);
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
  static const std::string  sync_comment;
  static const std::string  exec_comment;
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
  std::string               cas_var (void);
  std::string               sync_var (const word, const word);
  std::string               sync_var (void);
  std::string               exit_var (void);

  /* variable declaration generators */
  void                      declare_heap_var (void);
  void                      declare_accu_vars (void);
  void                      declare_mem_vars (void);

  void                      declare_stmt_vars (void);
  void                      declare_thread_vars (void);
  void                      declare_exec_vars (void);
  void                      declare_cas_var (void);
  void                      declare_sync_vars (void);

  /* expression generators */
  std::string               assign_var (std::string, std::string);

  std::string               assign_accu (std::string);
  std::string               assign_mem (std::string);

  /* common encodings */
  void                      add_initial_state (void);
  void                      add_initial_statement_activation (void);

  void                      add_synchronization_constraints (void);

  /* adds a section header comment to the formula */
  void                      add_comment_section (const std::string &);
  void                      add_comment_subsection (const std::string &);

  /* collects jump targets used in the current program */
  void                      collect_sync_stmts (void);

  virtual void              encode (void);
};

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
struct SMTLibEncoderFunctional : public SMTLibEncoder
{
  /* constructs an SMTLibEncoderFunctional for the given program and bound */
  SMTLibEncoderFunctional (const ProgramListPtr, unsigned long);

  std::unordered_map<word, std::vector<word>> accu_altering_pcs;
  std::unordered_map<word, std::vector<word>> mem_altering_pcs;
  std::unordered_map<word, std::vector<word>> heap_altering_pcs;

  void                add_statement_activation (void);
  void                add_thread_scheduling (void);
  void                add_statement_execution (void);
  void                add_exit_call (void);
  void                add_state_update (void);

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
#endif
