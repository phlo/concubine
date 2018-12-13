#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <sstream>
#include <unordered_set>

#include "program.hh"

/*******************************************************************************
 * Encodes the given Program into a SMT formula.
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
  std::unordered_map<
    word,
    std::unordered_map<
      word,
      std::unordered_set<InstructionPtr>
    >
  > predecessors;

  /*****************************************************************************
   * private functions
  *****************************************************************************/

  /* double-dispatched instruction encoding functions */
  virtual void        encode (Load &) = 0;
  virtual void        encode (Store &) = 0;

  virtual void        encode (Add &) = 0;
  virtual void        encode (Addi &) = 0;
  virtual void        encode (Sub &) = 0;
  virtual void        encode (Subi &) = 0;

  virtual void        encode (Cmp &) = 0;
  virtual void        encode (Jmp &) = 0;
  virtual void        encode (Jz &) = 0;
  virtual void        encode (Jnz &) = 0;
  virtual void        encode (Js &) = 0;
  virtual void        encode (Jns &) = 0;
  virtual void        encode (Jnzns &) = 0;

  virtual void        encode (Mem &) = 0;
  virtual void        encode (Cas &) = 0;

  virtual void        encode (Sync &) = 0;
  virtual void        encode (Exit &) = 0;

  /* collects jump targets used in the current program */
  void                collectPredecessors (void);

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

  static const std::string  heap_comment;
  static const std::string  accu_comment;
  static const std::string  mem_comment;

  /* state variable generators */
  std::string               heap_var (void);
  std::string               accu_var (void);
  std::string               mem_var (void);

  /* transition variable generators */
  std::string               thread_var (void);
  std::string               stmt_var (void);
  std::string               exec_var (void);
  std::string               cas_var (void);
  std::string               sync_var (void);
  std::string               exit_var (void);

  /* variable declaration generators */
  void                      declare_heap (void);
  void                      declare_accu (void);
  void                      declare_mem (void);

  /* expression generators */
  std::string               assign_var (std::string, std::string);

  std::string               assign_accu (std::string);
  std::string               assign_mem (std::string);

  /* common encodings */
  void                      set_logic_and_add_globals (void);
  void                      initial_state (void);

  /* adds a section header comment to the formula */
  void                      add_comment_section (const char *);
};

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
struct SMTLibEncoderFunctional : public SMTLibEncoder
{
  /* constructs an SMTLibEncoderFunctional for the given program and bound */
  SMTLibEncoderFunctional (const ProgramListPtr, unsigned long);

  /* double-dispatched instruction encoding functions */
  virtual void        encode (Load &);
  virtual void        encode (Store &);

  virtual void        encode (Add &);
  virtual void        encode (Addi &);
  virtual void        encode (Sub &);
  virtual void        encode (Subi &);

  virtual void        encode (Cmp &);
  virtual void        encode (Jmp &);
  virtual void        encode (Jz &);
  virtual void        encode (Jnz &);
  virtual void        encode (Js &);
  virtual void        encode (Jns &);
  virtual void        encode (Jnzns &);

  virtual void        encode (Mem &);
  virtual void        encode (Cas &);

  virtual void        encode (Sync &);
  virtual void        encode (Exit &);

  /*****************************************************************************
   * public functions
  *****************************************************************************/

  /* encodes the whole machine configuration */
  virtual void        encode (void);
};
#endif
