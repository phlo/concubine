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
  Encoder (ProgramList &, unsigned long);

  /* SMT formula */
  std::ostringstream  formula;

  /* reference to the programs being verified (index == thread id) */
  ProgramList & programs;

  /* bound */
  unsigned long bound;

  /*****************************************************************************
   * private functions
  *****************************************************************************/

  /* double-dispatched instruction encoding functions */
  virtual void  encode (Load &) = 0;
  virtual void  encode (Store &) = 0;

  virtual void  encode (Add &) = 0;
  virtual void  encode (Addi &) = 0;
  virtual void  encode (Sub &) = 0;
  virtual void  encode (Subi &) = 0;

  virtual void  encode (Cmp &) = 0;
  virtual void  encode (Jmp &) = 0;
  virtual void  encode (Jz &) = 0;
  virtual void  encode (Jnz &) = 0;
  virtual void  encode (Js &) = 0;
  virtual void  encode (Jns &) = 0;
  virtual void  encode (Jnzns &) = 0;

  virtual void  encode (Mem &) = 0;
  virtual void  encode (Cas &) = 0;

  virtual void  encode (Sync &) = 0;
  virtual void  encode (Exit &) = 0;

  /*****************************************************************************
   * public functions
  *****************************************************************************/

  /* encodes the whole machine configuration */
  virtual void  encode (void);

  /* print the SMT formula to stdout */
  void          print (void);

  /* returns the SMT formula as string */
  std::string   toString (void);
};

/*******************************************************************************
 * EncoderPtr
 ******************************************************************************/
typedef std::shared_ptr<Encoder> EncoderPtr;

/*******************************************************************************
 * SMT-Lib v2.5 Encoder
 ******************************************************************************/
struct SMTLibEncoder : public Encoder
{
  /* stores program state var names for a slim double-dispatch interface */
  struct State
    {
      std::string     activator;
      std::string     mem;
      std::string     accu;
      std::string     heap;
    };

  /* constructs an Encoder for the given program and bound */
  SMTLibEncoder (ProgramList &, unsigned long);

  /*****************************************************************************
   * variables
  *****************************************************************************/

  /* SMT formula in SMT-LIB v2 format */
  // std::ostringstream  formula;

  /* reference to the programs being verified (index == thread id) */
  // ProgramList &       programs;

  /* bound */
  // unsigned long       bound;

  /* current thread id */
  word                thread;

  /* current step */
  unsigned long       step;

  /* current pc */
  word                pc;

  /* current state (for a slim double-dispatch encoding interface) */
  State               cur;

  /* old state (for a slim double-dispatch encoding interface) */
  State               old;

  /* pcs of predecessor for each statement */
  std::unordered_map<word, std::unordered_set<word>> predecessors;

  /*****************************************************************************
   * private functions
  *****************************************************************************/

  /* collects jump targets used in the current program */
  void                collectPredecessors (void);

  /* adds smt file header (commented program and logic declaration) */
  void                addHeader (void);

  /* adds thread activation variable declarations to formula buffer */
  void                addThreadDeclarations (void);

  /* adds statement activation variable declarations to formula buffer */
  void                addStmtDeclarations (void);

  /* adds mem variable declarations to formula buffer */
  void                addMemDeclarations (void);

  /* adds accu variable declarations to formula buffer */
  void                addAccuDeclarations (void);

  /* adds heap variable declarations to formula buffer */
  void                addHeapDeclarations (void);

  /* adds exit variable declarations to formula buffer */
  void                addExitDeclarations (void);

  /* adds cardinality constraints for thread activation per step */
  void                addThreadConstraints (void);

  /* helper to simplify asserting an expression */
  std::string         imply (std::string, std::string);

  /* helper to simplify encoding of (indirect) loads */
  std::string         load (Load &);

  /* helper to simplify assignment of an arbitrary variable */
  std::string         assignVariable (std::string, std::string);

  /* adds mem register restoration for the current statement */
  void                restoreMem (void);

  /* adds accu restoration for the current statement */
  void                restoreAccu (void);

  /* adds heap restoration for the current statement */
  void                restoreHeap (void);

  /* adds assignment to the current statement's accu */
  void                assignAccu (std::string);

  /* adds assignment to the current statement's heap */
  void                assignHeap (std::string, std::string);

  /* adds assignment to the final variables for the current statement */
  void                assignFinal (void);

  /* adds activation for the target under the given condition */
  void                activate (std::string condition, std::string target);

  /* adds activation for the next statement */
  void                activateNext (void);

  /* adds conditional activation of target or next instruction */
  void                activateJump (std::string, word);

  /* encodes the current program (programs[thread]) */
  void                encodeProgram (void);

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
//
  // [> print the SMT-Lib v2 file to stdout <]
  // void                print (void);
//
  // [> returns the SMT-Lib v2 file as string <]
  // std::string         toString (void);
};

#endif
