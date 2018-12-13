#include "encoder.hh"

#include <iostream>
#include <regex>

#include "smtlib.hh"

using namespace std;

/*******************************************************************************
 * Encoder Base Class
 ******************************************************************************/
Encoder::Encoder (const ProgramListPtr p, unsigned long b) :
  programs(p),
  num_threads(p->size()),
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
SMTLibEncoder::SMTLibEncoder (
                              const ProgramListPtr p,
                              unsigned long b
                             ) : Encoder(p, b), step(0) {}

/* string constants ***********************************************************/
const string SMTLibEncoder::bv_sort =
  smtlib::bitvector(word_size);

const string SMTLibEncoder::exit_code_var =
  "exit_code";

const string SMTLibEncoder::heap_comment =
  "; heap states - heap_<step>";

const string SMTLibEncoder::accu_comment =
  "; accu states - accu_<step>_<thread>";

const string SMTLibEncoder::mem_comment =
  "; mem states - mem_<step>_<thread>";

/* state variable generators */
string SMTLibEncoder::heap_var ()
{
  return "heap_" + ::to_string(step);
}

string SMTLibEncoder::accu_var ()
{
  return "accu_" + ::to_string(step) + '_' + ::to_string(thread);
}

string SMTLibEncoder::mem_var ()
{
  return "mem_" + ::to_string(step) + '_' + ::to_string(thread);
}

/* variable declaration generators */
void SMTLibEncoder::declare_heap ()
{
  if (verbose)
    formula << heap_comment << eol;
  formula << smtlib::declare_array_var(heap_var(), bv_sort, bv_sort) << eol;
}

void SMTLibEncoder::declare_accu ()
{
  if (verbose)
    formula << accu_comment << eol;

  for (thread = 0; thread < num_threads; thread++)
    formula << smtlib::declare_var(accu_var(), bv_sort) << eol;
}

void SMTLibEncoder::declare_mem ()
{
  if (verbose)
    formula << mem_comment << eol;

  for (thread = 0; thread < num_threads; thread++)
    formula << smtlib::declare_var(mem_var(), bv_sort) << eol;
}

/* expression generators */
string SMTLibEncoder::assign_var (string var, string exp)
{
  return smtlib::assertion(smtlib::equality({var, exp}));
}

string SMTLibEncoder::assign_accu (string exp)
{
  return smtlib::assertion(smtlib::equality({accu_var(), exp}));
}

#define FOR_ALL_THREADS for (thread = 0; thread < num_threads; thread++)

/* common encodings */
void SMTLibEncoder::set_logic_and_add_globals ()
{
  /* set logic */
  formula << smtlib::set_logic() << eol << eol;

  /* declare exit code */
  if (verbose)
    formula << "; exit code" << eol;

  formula << smtlib::declare_bool_var(exit_code_var) << eol;
}

void SMTLibEncoder::initial_state ()
{
  if (verbose)
    add_comment_section("; initial state");

  /* accu */
  declare_accu();

  formula << eol;

  for (thread = 0; thread < num_threads; thread++)
    formula << assign_var(accu_var(), smtlib::word2hex(0)) << eol;

  formula << eol;

  /* CAS memory register */
  declare_mem();

  formula << eol;

  for (thread = 0; thread < num_threads; thread++)
    formula << assign_var(mem_var(), smtlib::word2hex(0)) << eol;

  formula << eol;

  /* heap */
  declare_heap();
}

void SMTLibEncoder::add_comment_section (const char * msg)
{
  formula << setw(80) << setfill(';') << eol;
  formula << msg << eol;
  formula << setw(80) << setfill(';') << eol << eol;
}

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
SMTLibEncoderFunctional::SMTLibEncoderFunctional (
                                                  const ProgramListPtr p,
                                                  unsigned long b
                                                 ) : SMTLibEncoder(p, b) {}

/* SMTLibEncoderFunctional::encode (void) *************************************/
void SMTLibEncoderFunctional::encode ()
{
  /* set logic and add global variable declarations */
  set_logic_and_add_globals();

  formula << eol;

  /* set initial state */
  initial_state();

  for (step = 1; step <= bound; step++)
    {
      /* statement activation */

      /* thread scheduling */

      /* synchronization constraints */

      /* statement execution */

      /* exit call */

      /* state update */
    }
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
