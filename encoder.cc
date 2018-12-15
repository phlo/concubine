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

void Encoder::iterate_threads (function<void(Program &)> fun)
{
  thread = 1;
  for (const ProgramPtr p_ptr : *programs)
    {
      fun(*p_ptr);
      thread++;
    }
}

void Encoder::preprocess ()
{
  iterate_threads([&] (Program & program) {
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

        /* collect exit calls */
        if (ExitPtr e = dynamic_pointer_cast<Exit>(program[pc]))
          exit_pcs[thread].push_back(pc);
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

string SMTLibEncoder::accu_var (const word k, const word t)
{
  return "accu_" + ::to_string(k) + '_' + ::to_string(t);
}

string SMTLibEncoder::accu_var ()
{
  return accu_var(step, thread);
}

string SMTLibEncoder::mem_var ()
{
  return "mem_" + ::to_string(step) + '_' + ::to_string(thread);
}

/* transition variable generators */
string SMTLibEncoder::stmt_var (const word k, const word t, const word p)
{
  return "stmt_"
    + ::to_string(k)
    + '_' + ::to_string(t)
    + '_' + ::to_string(p);
}

string SMTLibEncoder::stmt_var ()
{
  return stmt_var(step, thread, pc);
}

string SMTLibEncoder::thread_var (const word k, const word t)
{
  return "thread_" + ::to_string(k) + '_' + ::to_string(t);
}

string SMTLibEncoder::thread_var ()
{
  return thread_var(step, thread);
}

string SMTLibEncoder::exec_var (const word k, const word t, const word p)
{
  return "exec_"
    + ::to_string(k)
    + '_' + ::to_string(t)
    + '_' + ::to_string(p);
}

string SMTLibEncoder::exec_var ()
{
  return exec_var(step, thread, pc);
}

string SMTLibEncoder::sync_var (const word k, const word id)
{
  return "sync_" + ::to_string(k) + '_' + ::to_string(id);
}

string SMTLibEncoder::exit_var (const word k)
{
  return "exit_" + ::to_string(k);
}

string SMTLibEncoder::exit_var ()
{
  return exit_var(step);
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

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
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

void SMTLibEncoder::declare_exec_vars ()
{
  if (verbose)
    formula << exec_comment << eol;

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << smtlib::declare_bool_var(exec_var()) << eol;

    formula << eol;
  });
}

void SMTLibEncoder::declare_sync_vars ()
{
  if (verbose)
    formula << sync_comment << eol;

  for (const auto & s : sync_pcs)
    formula << smtlib::declare_bool_var(sync_var(step, s.first)) << eol;
}

void SMTLibEncoder::declare_exit_var ()
{
  if (verbose)
    formula << exit_comment << eol;

  formula << smtlib::declare_bool_var(exit_var()) << eol;
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

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << smtlib::assertion(pc ? smtlib::lnot(stmt_var()) : stmt_var())
        << eol;

    formula << eol;
  });
}

void SMTLibEncoder::add_synchronization_constraints ()
{
  if (verbose)
    add_comment_subsection("synchronization constraints");

  formula << eol;

  declare_sync_vars();

  formula << eol;

  if (verbose)
    formula << "; all threads synchronized?" << eol;

  for (const auto & [id, threads] : sync_pcs)
    {
      vector<string> stmt_args;
      vector<string> thread_args;

      for (const auto & [t, stmts] : threads)
        {
          thread_args.push_back(thread_var(step, t));

          for (const auto & s : stmts)
            stmt_args.push_back(stmt_var(step, t, s));
        }

      formula <<
        assign_var(
          sync_var(step, id),
          smtlib::land({
            smtlib::land(stmt_args),
            smtlib::lor(thread_args)})) <<
        eol;
    }

  formula << eol;

  if (verbose)
    formula << "; prevent scheduling of waiting threads" << eol;

  for (const auto & id : sync_pcs)
    for (const auto & [this_thread, this_stmts] : id.second)
      {
        vector<string> args;

        /* build disjunction of this threads SYNC statements */
        for (const auto & this_pc : this_stmts)
          args.push_back(stmt_var(step, this_thread, this_pc));

        string this_sync = args.size() > 1 ? smtlib::lor(args) : args[0];

        args.clear();

        /* build disjunction of the other threads negated SYNC statements */
        for (const auto & [other_thread, other_stmts] : id.second)
          {
            if (this_thread == other_thread)
              continue;

            for (const auto & other_pc : other_stmts)
              args.push_back(
                smtlib::lnot(stmt_var(step, other_thread, other_pc)));
          }

        string other_sync = args.size() > 1 ? smtlib::lor(args) : args[0];

        /* add thread blocking assertion */
        formula <<
          smtlib::assertion(
            smtlib::implication(
              smtlib::land({this_sync, other_sync}),
              smtlib::lnot(thread_var(step, this_thread)))) <<
          " ; barrier " << id.first << ": thread " << this_thread <<
          eol;
      }

  formula << eol;
}

// DEBUG: TODO remove
string sync_pcs_to_string (SMTLibEncoder & encoder)
{
  ostringstream ss;

  for (const auto & [id, threads] : encoder.sync_pcs)
    {
      ss << id << ": " << eol;

      for (const auto & [thread, pcs] : threads)
        {
          ss << "  " << thread << ":";
          for (const auto & pc : pcs)
            ss << " " << pc;
          ss << eol;
        }
    }

  return ss.str();
}

void SMTLibEncoder::add_statement_execution ()
{
  if (verbose)
    add_comment_subsection(
      "statement execution - shorthand for statement & thread activation");

  formula << eol;

  declare_exec_vars();

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        string activator = thread_var();

        if (SyncPtr s = dynamic_pointer_cast<Sync>(program[pc]))
          activator = sync_var(step, s->arg);

        formula <<
          assign_var(exec_var(), smtlib::land({stmt_var(), activator})) <<
          eol;
      }

    formula << eol;
  });
}

void SMTLibEncoder::add_comment_section (const string & msg)
{
  formula << setw(80) << setfill(';') << ';' << eol;
  formula << "; " << msg << eol;
  formula << setw(80) << setfill(';') << ';' << eol << eol;
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
    add_initial_statement_activation();
  else
    iterate_threads([&] (Program & program) {
      for (pc = 0; pc < program.size(); pc++)
        {
          /* statement reactivation */
          string expr =
            smtlib::land({
              stmt_var(step - 1, thread, pc),
              smtlib::lnot(exec_var(step - 1, thread, pc))});

          for (word prev : predecessors[thread][pc])
            {
              /* predecessor's execution variable */
              string val = exec_var(step - 1, thread, prev);

              /* build conjunction of execution variable and jump condition */
              if (JmpPtr j = dynamic_pointer_cast<Jmp>(program[prev]))
                {
                  /* JMP has no condition and returns an empty string */
                  string cond = j->encode(*this);

                  val = cond.empty() ? val : smtlib::land({val, cond});
                }

              /* add predecessor to the activation */
              expr = smtlib::ite(stmt_var(step - 1, thread, prev), val, expr);
            }

          formula << assign_var(stmt_var(), expr) << eol;
        }

      formula << eol;
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

void SMTLibEncoderFunctional::add_exit_call ()
{
  /* skip if step == 1 or EXIT isn't called at all */
  if (exit_pcs.empty() || step == 1)
    return;

  if (verbose)
    add_comment_subsection("exit call");

  formula << eol;

  declare_exit_var();

  formula << eol;

  /* assign exit variable */
  vector<string> args;

  if (step > 2)
    args.push_back(exit_var(step - 1));

  iterate_threads([&] {
    for (const word & exit_pc : exit_pcs[thread])
      args.push_back(exec_var(step - 1, thread, exit_pc));
  });

  formula << assign_var(exit_var(), smtlib::lor(args)) << eol << eol;

  /* assign exit code */
  iterate_threads([&] (Program & program) {
    for (const word & exit_pc : exit_pcs[thread])
      /* TODO: implication or ite? */
      formula <<
        smtlib::assertion(
          smtlib::implication(
            exec_var(step, thread, exit_pc),
            program[exit_pc]->encode(*this))) <<
        eol;
  });

  formula << eol;
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
      add_synchronization_constraints();

      /* statement execution */
      add_statement_execution();

      /* exit call */
      add_exit_call();

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
  return
      smtlib::lnot(
        smtlib::equality({
          accu_var(step - 1, thread),
          smtlib::word2hex(j.arg)}));
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
  return assign_var(exit_code_var, smtlib::word2hex(e.arg));
}
