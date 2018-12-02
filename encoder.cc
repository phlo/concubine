#include "encoder.hh"

#include <iostream>

#include "smtlib.hh"

using namespace std;

/*******************************************************************************
 * Encoder Base Class
 ******************************************************************************/
Encoder::Encoder (ProgramList & p, unsigned long b) :
  programs(p),
  bound(b)
{
}

/* Encoder::collectPredecessors (void) ****************************************/
void Encoder::collectPredecessors ()
{
  predecessors.clear();

  word length = programs[thread]->size();

  for (pc = 0; pc < length; pc++)
    {
      /* add previous statement if pc > 0 */
      if (pc > 0)
        predecessors[thread][pc].insert(pc - 1);

      /* add current pc to predecessors of target statement */
      /* NOTE: possible improvement: remove pc of JMP from successor before
       * adding to the target statement */
      if (JmpPtr j = dynamic_pointer_cast<Jmp>(programs[thread]->at(pc)))
        predecessors[thread][j->arg].insert(pc);
    }
}

/* Encoder::encode (void) *****************************************************/
void Encoder::encode () {}

/* Encoder::print (void) ******************************************************/
void Encoder::print ()
{
  cout << formula.str();
}

/* Encoder::toString (void) ***************************************************/
string Encoder::to_string ()
{
  return formula.str();
}

/*******************************************************************************
 * SMT-Lib v2.5 Program Encoder Class
 ******************************************************************************/
SMTLibEncoder::SMTLibEncoder (ProgramList & p, unsigned long b) :
  Encoder(p, b)
{}

/* SMTLibEncoder::encode (void) ***********************************************/
void SMTLibEncoder::encode ()
{
}

/* SMTLibEncoder::encode(Load &) **********************************************/
void SMTLibEncoder::encode (Load & l)
{
  (void) l;
}

/* SMTLibEncoder::encode(Store &) *********************************************/
void SMTLibEncoder::encode (Store & s)
{
  (void) s;
}

/* SMTLibEncoder::encode(Add &) ***********************************************/
void SMTLibEncoder::encode (Add & a)
{
  (void) a;
}

/* SMTLibEncoder::encode(Addi &) **********************************************/
void SMTLibEncoder::encode (Addi & a)
{
  (void) a;
}

/* SMTLibEncoder::encode(Sub &) ***********************************************/
void SMTLibEncoder::encode (Sub & s)
{
  (void) s;
}

/* SMTLibEncoder::encode(Subi &) **********************************************/
void SMTLibEncoder::encode (Subi & s)
{
  (void) s;
}

/* SMTLibEncoder::encode(Cmp &) ***********************************************/
void SMTLibEncoder::encode (Cmp & c)
{
  (void) c;
}

/* SMTLibEncoder::encode(Jmp &) ***********************************************/
void SMTLibEncoder::encode (Jmp & j)
{
  (void) j;
}

/* SMTLibEncoder::encode(Jz &) ************************************************/
void SMTLibEncoder::encode (Jz & j)
{
  (void) j;
}

/* SMTLibEncoder::encode(Jnz &) ***********************************************/
void SMTLibEncoder::encode (Jnz & j)
{
  (void) j;
}

/* SMTLibEncoder::encode(Js &) ************************************************/
void SMTLibEncoder::encode (Js & j)
{
  (void) j;
}

/* SMTLibEncoder::encode(Jns &) ***********************************************/
void SMTLibEncoder::encode (Jns & j)
{
  (void) j;
}

/* SMTLibEncoder::encode(Jnzns &) *********************************************/
void SMTLibEncoder::encode (Jnzns & j)
{
  (void) j;
}

/* SMTLibEncoder::encode(Mem &) ***********************************************/
void SMTLibEncoder::encode (Mem & m)
{
  (void) m;
}

/* SMTLibEncoder::encode(Cas &) ***********************************************/
void SMTLibEncoder::encode (Cas & c)
{
  (void) c;
}

/* SMTLibEncoder::encode(Sync &) **********************************************/
void SMTLibEncoder::encode (Sync & s)
{
  (void) s;
}

/* SMTLibEncoder::encode(Exit &) **********************************************/
void SMTLibEncoder::encode (Exit & e)
{
  (void) e;
}
