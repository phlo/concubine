#ifndef ENCODER_HH_
#define ENCODER_HH_

#include <sstream>
#include <unordered_set>

#include "instructionset.hh"

/* forward declarations */
class Program;

using namespace std;

/*******************************************************************************
 * SMT-Lib v2.5 Encoder
 *
 * Encodes the given Program into a SMT formula.
 ******************************************************************************/
namespace smtlib
{
  class Encoder
    {
      /* stores program state var names for a slim double-dispatch interface */
      struct State
        {
          string          activator;
          string          mem;
          string          accu;
          string          heap;
        };

      /* SMT formula in SMT-LIB v2 format */
      ostringstream       formula;

      /* reference to the program being verified */
      Program &           program;

      /* bound */
      unsigned long       bound;

      /* current step while encoding */
      unsigned long       step;

      /* current pc while encoding */
      word                pc;

      /* current state (for a slim double-dispatch encoding interface) */
      State               cur;

      /* old state (for a slim double-dispatch encoding interface) */
      State               old;

      /* pcs of predecessor for each statement */
      unordered_map<word, unordered_set<word>> predecessors;

      /* collects jump targets used in the program */
      void                collectPredecessors (void);


      /* adds smt file header (commented program and logic declaration) */
      void                addHeader (void);

      /* adds smt file footer (check-sat, get-model, etc.) */
      void                addFooter (void);

      /* adds activation variable declarations to formula buffer */
      void                addStmtDeclarations (void);

      /* adds mem variable declarations to formula buffer */
      void                addMemDeclarations (void);

      /* adds accu variable declarations to formula buffer */
      void                addAccuDeclarations (void);

      /* adds heap variable declarations to formula buffer */
      void                addHeapDeclarations (void);

      /* adds exit variable declarations to formula buffer */
      void                addExitDeclarations (void);


      /* helper to simplify asserting an expression */
      string              imply (string, string);

      /* helper to simplify encoding of (indirect) loads */
      string              load (Load &);

      /* helper to simplify assignment of an arbitrary variable */
      string              assignVariable (string, string);

      /* adds mem register restoration for the current statement */
      void                restoreMem (void);

      /* adds accu restoration for the current statement */
      void                restoreAccu (void);

      /* adds heap restoration for the current statement */
      void                restoreHeap (void);

      /* adds assignment to the current statement's accu */
      void                assignAccu (string);

      /* adds assignment to the current statement's heap */
      void                assignHeap (string, string);

      /* adds assignment to the final variables for the current statement */
      void                assignFinal (void);

      /* adds activation for the target under the given condition */
      void                activate (string condition, string target);

      /* adds activation for the next statement */
      void                activateNext (void);

      /* adds conditional activation of target or next instruction */
      void                activateJump (string, word);

    public:
      /* constructor */
      Encoder (Program &, unsigned long);

      /* print the SMT-Lib v2 file to stdout */
      void                print (void);

      /* returns the SMT-Lib v2 file as string */
      string              toString (void);

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
    };

  /*****************************************************************************
   * EncoderPtr
   ****************************************************************************/
  typedef shared_ptr<Encoder> EncoderPtr;
};

#endif
