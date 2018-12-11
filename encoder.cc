#include "encoder.hh"

#include <iostream>
#include <regex>

#include "smtlib.hh"

using namespace std;
using namespace smtlib;

/*******************************************************************************
 * Encoder Base Class
 ******************************************************************************/
Encoder::Encoder (const ProgramListPtr p, unsigned long b) :
  programs(p),
  bound(b)
{}

/* Encoder::collectPredecessors (void) ****************************************/
void Encoder::collectPredecessors ()
{
  predecessors.clear();

  word length = programs->at(thread)->size();

  for (pc = 0; pc < length; pc++)
    {
      /* add previous statement if pc > 0 */
      if (pc > 0)
        predecessors[thread][pc].insert(programs->at(thread)->at(pc - 1u));

      /* add current pc to predecessors of target statement */
      /* NOTE: possible improvement: remove pc of JMP from successor before
       * adding to the target statement */
      if (JmpPtr j = dynamic_pointer_cast<Jmp>(programs->at(thread)->at(pc)))
        predecessors[thread][j->arg].insert(programs->at(thread)->at(pc));
    }
}

/* Encoder::encode (void) *****************************************************/
void Encoder::encode () {}

/* Encoder::print (void) ******************************************************/
void Encoder::print () { cout << formula.str(); }

/* Encoder::to_string (void) **************************************************/
string Encoder::to_string () { return formula.str(); }

/*******************************************************************************
 * SMT-Lib v2.5 Encoder Base Class
 ******************************************************************************/

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
SMTLibEncoderFunctional::SMTLibEncoderFunctional (
                                                  const ProgramListPtr p,
                                                  unsigned long b
                                                 )
  : Encoder(p, b)
{}

/* SMTLibEncoderFunctional::encode (void) *************************************/
void SMTLibEncoderFunctional::encode ()
{
  /* set logic */
  formula << smtlib::set_logic();

  /* declare exit code */

  /* set initial state */

  /* statement activation */

  /* thread scheduling */

  /* synchronization constraints */

  /* statement execution */

  /* exit call */

  /* state update */
}

/* SMTLibEncoderFunctional::encode (Load &) ***********************************/
void SMTLibEncoderFunctional::encode (Load & l)
{
  (void) l;
}

/* SMTLibEncoderFunctional::encode (Store &) **********************************/
void SMTLibEncoderFunctional::encode (Store & s)
{
  (void) s;
}

/* SMTLibEncoderFunctional::encode (Add &) ************************************/
void SMTLibEncoderFunctional::encode (Add & a)
{
  (void) a;
}

/* SMTLibEncoderFunctional::encode (Addi &) ***********************************/
void SMTLibEncoderFunctional::encode (Addi & a)
{
  (void) a;
}

/* SMTLibEncoderFunctional::encode (Sub &) ************************************/
void SMTLibEncoderFunctional::encode (Sub & s)
{
  (void) s;
}

/* SMTLibEncoderFunctional::encode (Subi &) ***********************************/
void SMTLibEncoderFunctional::encode (Subi & s)
{
  (void) s;
}

/* SMTLibEncoderFunctional::encode (Cmp &) ************************************/
void SMTLibEncoderFunctional::encode (Cmp & c)
{
  (void) c;
}

/* SMTLibEncoderFunctional::encode (Jmp &) ************************************/
void SMTLibEncoderFunctional::encode (Jmp & j)
{
  (void) j;
}

/* SMTLibEncoderFunctional::encode (Jz &) *************************************/
void SMTLibEncoderFunctional::encode (Jz & j)
{
  (void) j;
}

/* SMTLibEncoderFunctional::encode (Jnz &) ************************************/
void SMTLibEncoderFunctional::encode (Jnz & j)
{
  (void) j;
}

/* SMTLibEncoderFunctional::encode (Js &) *************************************/
void SMTLibEncoderFunctional::encode (Js & j)
{
  (void) j;
}

/* SMTLibEncoderFunctional::encode (Jns &) ************************************/
void SMTLibEncoderFunctional::encode (Jns & j)
{
  (void) j;
}

/* SMTLibEncoderFunctional::encode (Jnzns &) **********************************/
void SMTLibEncoderFunctional::encode (Jnzns & j)
{
  (void) j;
}

/* SMTLibEncoderFunctional::encode (Mem &) ************************************/
void SMTLibEncoderFunctional::encode (Mem & m)
{
  (void) m;
}

/* SMTLibEncoderFunctional::encode (Cas &) ************************************/
void SMTLibEncoderFunctional::encode (Cas & c)
{
  (void) c;
}

/* SMTLibEncoderFunctional::encode (Sync &) ***********************************/
void SMTLibEncoderFunctional::encode (Sync & s)
{
  (void) s;
}

/* SMTLibEncoderFunctional::encode (Exit &) ***********************************/
void SMTLibEncoderFunctional::encode (Exit & e)
{
  (void) e;
}
