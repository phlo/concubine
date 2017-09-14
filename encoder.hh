#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <sstream>
#include <unordered_set>

#include "program.hh"

/*******************************************************************************
 * SMT-Lib v2.5 Encoder
 *
 * Encodes the given Program into a SMT formula.
 ******************************************************************************/
namespace smtlib
{
  struct Encoder
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
      Encoder (ProgramList &, unsigned long);

      /*************************************************************************
       * variables
      *************************************************************************/

      /* SMT formula in SMT-LIB v2 format */
      std::ostringstream  formula;

      /* reference to the programs being verified (index == thread id) */
      ProgramList &       programs;

      /* bound */
      unsigned long       bound;

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

      /*************************************************************************
       * private functions
      *************************************************************************/

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
      void                encode (Load &);
      void                encode (Store &);

      void                encode (Add &);
      void                encode (Addi &);
      void                encode (Sub &);
      void                encode (Subi &);

      void                encode (Cmp &);
      void                encode (Jmp &);
      void                encode (Jz &);
      void                encode (Jnz &);
      void                encode (Js &);
      void                encode (Jns &);
      void                encode (Jnzns &);

      void                encode (Mem &);
      void                encode (Cas &);

      void                encode (Sync &);
      void                encode (Exit &);

      /*************************************************************************
       * public functions
      *************************************************************************/

      /* encodes the whole machine configuration */
      void                encode (void);

      /* print the SMT-Lib v2 file to stdout */
      void                print (void);

      /* returns the SMT-Lib v2 file as string */
      std::string         toString (void);
    };

  /*****************************************************************************
   * EncoderPtr
   ****************************************************************************/
  typedef std::shared_ptr<Encoder> EncoderPtr;
}

#endif
