#include "encoder.hh"

#include <iostream>

#include "smtlib.hh"

using namespace std;

/*******************************************************************************
 * Encoder Base Class
 ******************************************************************************/
Encoder::Encoder (const ProgramListPtr p, unsigned long b) :
  programs(p),
  num_threads(p->size()),
  bound(b)
{
  preprocess();
}

void Encoder::iterate_threads (function<void()> fun)
{
  for (thread = 1; thread <= num_threads; thread++)
    fun();
}

void Encoder::iterate_threads (function<void(ProgramPtr)> fun)
{
  thread = 1;
  for (const ProgramPtr p_ptr : *programs)
    {
      fun(p_ptr);
      thread++;
    }
}

void Encoder::preprocess ()
{
  iterate_threads([&] (ProgramPtr p) {
    Program & program = *p;
    for (pc = 0; pc < program.size(); pc++)
      {
        /* collect predecessors */
        if (pc > 0)
          predecessors[thread][pc].insert(pc - 1u);

        if (JmpPtr j = dynamic_pointer_cast<Jmp>(program[pc]))
          predecessors[thread][j->arg].insert(pc);

        /* collect sync statemets */
        if (SyncPtr s = dynamic_pointer_cast<Sync>(program[pc]))
          sync_pcs[s->arg][thread].insert(pc);
      }
  });
}

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

const string SMTLibEncoder::stmt_comment =
  "; statement activation variables - stmt_<step>_<thread>_<pc>";

const string SMTLibEncoder::thread_comment =
  "; thread activation variables - thread_<step>_<thread>";

const string SMTLibEncoder::sync_comment =
  "; sync variables - sync_<step>_<id>";

const string SMTLibEncoder::exec_comment =
  "; statement execution variables - exec_<step>_<thread>_<pc>";

const string SMTLibEncoder::exit_comment =
  "; exit variable - exit_<step>";

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

/* transition variable generators */
string SMTLibEncoder::stmt_var ()
{
  return "stmt_"
    + ::to_string(step)
    + '_' + ::to_string(thread)
    + '_' + ::to_string(pc);
}

string SMTLibEncoder::thread_var ()
{
  return "thread_" + ::to_string(step) + '_' + ::to_string(thread);
}

string SMTLibEncoder::exit_var ()
{
  return "exit_" + ::to_string(step);
}

/* variable declaration generators */
void SMTLibEncoder::declare_heap_var ()
{
  if (verbose)
    formula << heap_comment << eol;

  formula << smtlib::declare_array_var(heap_var(), bv_sort, bv_sort) << eol;
}

void SMTLibEncoder::declare_accu_vars ()
{
  if (verbose)
    formula << accu_comment << eol;

  iterate_threads([&] {
    formula << smtlib::declare_var(accu_var(), bv_sort) << eol;
  });
}

void SMTLibEncoder::declare_mem_vars ()
{
  if (verbose)
    formula << mem_comment << eol;

  iterate_threads([&] {
    formula << smtlib::declare_var(mem_var(), bv_sort) << eol;
  });
}

void SMTLibEncoder::declare_stmt_vars ()
{
  if (verbose)
    formula << stmt_comment << eol;

  iterate_threads([&] (ProgramPtr p) {
    for (pc = 0; pc < p->size(); pc++)
      formula << smtlib::declare_bool_var(stmt_var()) << eol;

    formula << eol;
  });
}

void SMTLibEncoder::declare_thread_vars ()
{
  if (verbose)
    formula << thread_comment << eol;

  iterate_threads([&] {
    formula << smtlib::declare_bool_var(thread_var()) << eol;
  });
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

/* common encodings */
void SMTLibEncoder::add_initial_state ()
{
  if (verbose)
    add_comment_section("initial state");

  /* accu */
  declare_accu_vars();

  formula << eol;

  iterate_threads([&] {
    formula << assign_var(accu_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* CAS memory register */
  declare_mem_vars();

  formula << eol;

  iterate_threads([&] {
    formula << assign_var(mem_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* heap */
  declare_heap_var();
}

void SMTLibEncoder::add_initial_statement_activation ()
{
  formula << "; initial statement activation" << eol;

  iterate_threads([&] (ProgramPtr p) {
    for (pc = 0; pc < p->size(); pc++)
      formula
        << smtlib::assertion(pc ? smtlib::lnot(stmt_var()) : stmt_var())
        << eol;

    formula << eol;
  });
}

void SMTLibEncoder::add_comment_section (const string & msg)
{
  formula << setw(79) << setfill(';') << ';' << eol;
  formula << "; " << msg << eol;
  formula << setw(79) << setfill(';') << ';' << eol << eol;
}

void SMTLibEncoder::add_comment_subsection (const string & msg)
{
  formula << left << setfill(';') << setw(80) << ("; " + msg + " ") << eol;
}

void SMTLibEncoder::encode ()
{
  /* set logic */
  formula << smtlib::set_logic() << eol << eol;

  /* declare exit code */
  if (verbose)
    formula << "; exit code" << eol;

  formula << smtlib::declare_bool_var(exit_code_var) << eol << eol;

  /* set initial state */
  add_initial_state();
}

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
SMTLibEncoderFunctional::SMTLibEncoderFunctional (
                                                  const ProgramListPtr p,
                                                  unsigned long b
                                                 ) : SMTLibEncoder(p, b) {}

void SMTLibEncoderFunctional::add_statement_activation ()
{
  if (verbose)
    add_comment_subsection("statement activation");

  formula << eol;

  declare_stmt_vars();

  if (step == 1)
    {
      add_initial_statement_activation();
      return;
    }

  iterate_threads([&] (ProgramPtr p) {
    Program & program = *p;
    for (pc = 0; pc < program.size(); pc++)
      {
        // TODO
        for (word pre : predecessors[thread][pc])
          {
            if (JmpPtr j = dynamic_pointer_cast<Jmp>(program[pre]))
              {
                j->encode(*this);
              }
            else
              {
              }
          }
      }
  });
}

void SMTLibEncoderFunctional::add_thread_scheduling ()
{
  vector<string> variables;

  iterate_threads([&] { variables.push_back(thread_var()); });

  variables.push_back(exit_var());

  if (verbose)
    add_comment_subsection("thread scheduling");

  formula << eol;

  declare_thread_vars();

  formula
    << eol
    << (num_threads > 5
      ? smtlib::card_constraint_sinz(variables)
      : smtlib::card_constraint_naive(variables))
    << eol;
}

/* SMTLibEncoderFunctional::encode (void) *************************************/
void SMTLibEncoderFunctional::encode ()
{
  /* set logic and add common variable declarations */
  SMTLibEncoder::encode();

  formula << eol;

  for (step = 1; step <= bound; step++)
    {
      add_comment_section("step " + ::to_string(step));

      /* statement activation */
      add_statement_activation();

      /* thread scheduling */
      add_thread_scheduling();

      /* synchronization constraints */

      /* statement execution */

      /* exit call */

      /* state update */
    }
}

/* SMTLibEncoderFunctional::encode (Load &) ***********************************/
string SMTLibEncoderFunctional::encode (Load & l)
{
  (void) l;
  return "";
}

/* SMTLibEncoderFunctional::encode (Store &) **********************************/
string SMTLibEncoderFunctional::encode (Store & s)
{
  (void) s;
  return "";
}

/* SMTLibEncoderFunctional::encode (Add &) ************************************/
string SMTLibEncoderFunctional::encode (Add & a)
{
  (void) a;
  return "";
}

/* SMTLibEncoderFunctional::encode (Addi &) ***********************************/
string SMTLibEncoderFunctional::encode (Addi & a)
{
  (void) a;
  return "";
}

/* SMTLibEncoderFunctional::encode (Sub &) ************************************/
string SMTLibEncoderFunctional::encode (Sub & s)
{
  (void) s;
  return "";
}

/* SMTLibEncoderFunctional::encode (Subi &) ***********************************/
string SMTLibEncoderFunctional::encode (Subi & s)
{
  (void) s;
  return "";
}

/* SMTLibEncoderFunctional::encode (Cmp &) ************************************/
string SMTLibEncoderFunctional::encode (Cmp & c)
{
  (void) c;
  return "";
}

/* SMTLibEncoderFunctional::encode (Jmp &) ************************************/
string SMTLibEncoderFunctional::encode (Jmp & j)
{
  (void) j;
  return "";
}

/* SMTLibEncoderFunctional::encode (Jz &) *************************************/
string SMTLibEncoderFunctional::encode (Jz & j)
{
  (void) j;
  return "";
}

/* SMTLibEncoderFunctional::encode (Jnz &) ************************************/
string SMTLibEncoderFunctional::encode (Jnz & j)
{
  (void) j;
  return "";
}

/* SMTLibEncoderFunctional::encode (Js &) *************************************/
string SMTLibEncoderFunctional::encode (Js & j)
{
  (void) j;
  return "";
}

/* SMTLibEncoderFunctional::encode (Jns &) ************************************/
string SMTLibEncoderFunctional::encode (Jns & j)
{
  (void) j;
  return "";
}

/* SMTLibEncoderFunctional::encode (Jnzns &) **********************************/
string SMTLibEncoderFunctional::encode (Jnzns & j)
{
  (void) j;
  return "";
}

/* SMTLibEncoderFunctional::encode (Mem &) ************************************/
string SMTLibEncoderFunctional::encode (Mem & m)
{
  (void) m;
  return "";
}

/* SMTLibEncoderFunctional::encode (Cas &) ************************************/
string SMTLibEncoderFunctional::encode (Cas & c)
{
  (void) c;
  return "";
}

/* SMTLibEncoderFunctional::encode (Sync &) ***********************************/
string SMTLibEncoderFunctional::encode (Sync & s)
{
  (void) s;
  return "";
}

/* SMTLibEncoderFunctional::encode (Exit &) ***********************************/
string SMTLibEncoderFunctional::encode (Exit & e)
{
  (void) e;
  return "";
}
