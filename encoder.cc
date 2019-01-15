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

void Encoder::iterate_threads_reverse (function<void(Program &)> fun)
{
  thread = num_threads;
  for (auto rit = programs->rbegin(); rit != programs->rend(); ++rit)
    {
      fun(**rit);
      thread--;
    }
}

void Encoder::preprocess ()
{
  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        /* collect predecessors */
        if (pc > 0)
          if (!dynamic_pointer_cast<Exit>(program[pc - 1u]))
            if (program[pc - 1u]->get_symbol() != "JMP")
              predecessors[thread][pc].insert(pc - 1u);

        if (JmpPtr j = dynamic_pointer_cast<Jmp>(program[pc]))
          predecessors[thread][j->arg].insert(pc);

        /* collect CAS statemets */
        if (CasPtr c = dynamic_pointer_cast<Cas>(program[pc]))
          cas_threads.insert(thread);

        /* collect sync statemets */
        if (SyncPtr s = dynamic_pointer_cast<Sync>(program[pc]))
          sync_pcs[s->arg][thread].insert(pc);

        /* collect exit calls */
        if (ExitPtr e = dynamic_pointer_cast<Exit>(program[pc]))
          exit_pcs[thread].insert(pc);
      }
  });
}

/* Encoder::print (void) ******************************************************/
void Encoder::print () { cout << formula.str(); }

/* Encoder::str (void) ********************************************************/
string Encoder::str () { return formula.str(); }

/* DEBUG **********************************************************************/
string Encoder::predecessors_to_string ()
{
  ostringstream ss;

  for (const auto & [_thread, _pcs] : predecessors)
    for (const auto & [_pc, _predecessors] : _pcs)
      {
        ss << "thread " << _thread << " @ " << _pc << " :";
        for (const auto & prev : _predecessors)
          ss << " " << prev;
        ss << eol;
      }

  return ss.str();
}

string Encoder::sync_pcs_to_string ()
{
  ostringstream ss;

  for (const auto & [id, threads] : sync_pcs)
    {
      ss << "sync " << id << ": " << eol;
      for (const auto & [_thread, pcs] : threads)
        {
          ss << "  " << _thread << ":";
          for (const auto & _pc : pcs)
            ss << " " << _pc;
          ss << eol;
        }
    }

  return ss.str();
}

string Encoder::exit_pcs_to_string ()
{
  ostringstream ss;

  for (const auto & [_thread, pcs] : exit_pcs)
    {
      ss << "thread " << _thread << ":";
      for (const auto & _pc : pcs)
        ss << ' ' << _pc;
      ss << eol;
    }

  return ss.str();
}

/*******************************************************************************
 * SMT-Lib v2.5 Encoder Base Class
 ******************************************************************************/
SMTLibEncoder::SMTLibEncoder (
                              const ProgramListPtr p,
                              unsigned long b
                             ) :
  Encoder(p, b),
  step(0),
  use_sinz_constraint(num_threads > 5)
{}

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

const string SMTLibEncoder::exec_comment =
  "; statement execution variables - exec_<step>_<thread>_<pc>";

const string SMTLibEncoder::cas_comment =
  "; CAS condition - cas_<step>_<thread>";

const string SMTLibEncoder::sync_comment =
  "; sync variables - sync_<step>_<id>";

const string SMTLibEncoder::exit_comment =
  "; exit flag - exit_<step>";

/* state variable generators */
string SMTLibEncoder::heap_var (const word k)
{
  return "heap_" + to_string(k);
}

string SMTLibEncoder::heap_var ()
{
  return heap_var(step);
}

string SMTLibEncoder::accu_var (const word k, const word t)
{
  return "accu_" + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::accu_var ()
{
  return accu_var(step, thread);
}

string SMTLibEncoder::mem_var (const word k, const word t)
{
  return "mem_" + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::mem_var ()
{
  return mem_var(step, thread);
}

/* transition variable generators */
string SMTLibEncoder::stmt_var (const word k, const word t, const word p)
{
  return "stmt_"
    + to_string(k)
    + '_' + to_string(t)
    + '_' + to_string(p);
}

string SMTLibEncoder::stmt_var ()
{
  return stmt_var(step, thread, pc);
}

string SMTLibEncoder::thread_var (const word k, const word t)
{
  return "thread_" + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::thread_var ()
{
  return thread_var(step, thread);
}

string SMTLibEncoder::exec_var (const word k, const word t, const word p)
{
  return "exec_"
    + to_string(k)
    + '_' + to_string(t)
    + '_' + to_string(p);
}

string SMTLibEncoder::exec_var ()
{
  return exec_var(step, thread, pc);
}

string SMTLibEncoder::cas_var (const word k, const word t)
{
  return "cas_" + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::cas_var ()
{
  return cas_var(step, thread);
}

string SMTLibEncoder::sync_var (const word k, const word id)
{
  return "sync_" + to_string(k) + '_' + to_string(id);
}

string SMTLibEncoder::exit_var (const word k)
{
  return "exit_" + to_string(k);
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

  formula
    << smtlib::declare_array_var(heap_var(), bv_sort, bv_sort)
    << eol << eol;
}

void SMTLibEncoder::declare_accu_vars ()
{
  if (verbose)
    formula << accu_comment << eol;

  iterate_threads([&] {
    formula << smtlib::declare_bv_var(accu_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLibEncoder::declare_mem_vars ()
{
  if (verbose)
    formula << mem_comment << eol;

  iterate_threads([&] {
    formula << smtlib::declare_bv_var(mem_var(), word_size) << eol;
  });

  formula << eol;
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

void SMTLibEncoder::declare_cas_vars ()
{
  if (cas_threads.empty())
    return;

  if (verbose)
    formula << cas_comment << eol;

  iterate_threads([&] {
    if (cas_threads.find(thread) != cas_threads.end())
      formula << smtlib::declare_bool_var(cas_var()) << eol;
  });

  formula << eol;
}

void SMTLibEncoder::declare_sync_vars ()
{
  if (verbose)
    formula << sync_comment << eol;

  for (const auto & s : sync_pcs)
    formula << smtlib::declare_bool_var(sync_var(step, s.first)) << eol;

  formula << eol;
}

void SMTLibEncoder::declare_exit_var ()
{
  if (verbose)
    formula << exit_comment << eol;

  formula << smtlib::declare_bool_var(exit_var()) << eol << eol;
}

/* expression generators */
string SMTLibEncoder::assign_var (string var, string exp)
{
  return smtlib::assertion(smtlib::equality({var, exp}));
}

/* common encodings */
void SMTLibEncoder::add_initial_state ()
{
  if (verbose)
    formula << smtlib::comment_section("initial state");

  /* accu */
  declare_accu_vars();

  iterate_threads([&] {
    formula << assign_var(accu_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* CAS memory register */
  declare_mem_vars();

  iterate_threads([&] {
    formula << assign_var(mem_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* heap */
  declare_heap_var();
}

void SMTLibEncoder::add_initial_statement_activation ()
{
  if (verbose)
    formula << "; initial statement activation" << eol;

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << smtlib::assertion(pc ? smtlib::lnot(stmt_var()) : stmt_var())
        << eol;

    formula << eol;
  });
}

void SMTLibEncoder::add_thread_scheduling ()
{
  vector<string> variables;

  /* add thread activation variables */
  iterate_threads([&] { variables.push_back(thread_var()); });

  /* add exit flag */
  if (step > 1 && !exit_pcs.empty())
    variables.push_back(exit_var());

  if (verbose)
    formula << smtlib::comment_subsection("thread scheduling");

  declare_thread_vars();

  formula
    << eol
    << (use_sinz_constraint
      ? smtlib::card_constraint_sinz(variables)
      : smtlib::card_constraint_naive(variables))
    << eol;
}

void SMTLibEncoder::add_synchronization_constraints ()
{
  if (verbose)
    formula << smtlib::comment_subsection("synchronization constraints");

  declare_sync_vars();

  if (verbose)
    formula << "; all threads synchronized?" << eol;

  for (const auto & [id, threads] : sync_pcs)
    {
      vector<string> sync_args;
      vector<string> thread_args;

      for (const auto & [t, stmts] : threads)
        {
          vector<string> args;

          thread_args.push_back(thread_var(step, t));

          for (const auto & s : stmts)
            args.push_back(stmt_var(step, t, s));

          sync_args.push_back(args.size() > 1 ? smtlib::lor(args) : args[0]);
        }

      sync_args.push_back(smtlib::lor(thread_args));

      formula <<
        assign_var(
          sync_var(step, id),
          smtlib::land(sync_args)) <<
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

        /* add thread blocking assertion */
        formula <<
          smtlib::assertion(
            smtlib::implication(
              smtlib::land({this_sync, smtlib::lnot(sync_var(step, id.first))}),
              smtlib::lnot(thread_var(step, this_thread))));

        if (verbose)
          formula << " ; barrier " << id.first << ": thread " << this_thread;

        formula << eol;
      }

  formula << eol;
}

void SMTLibEncoder::add_statement_execution ()
{
  if (verbose)
    formula << smtlib::comment_subsection(
      "statement execution - shorthand for statement & thread activation");

  declare_exec_vars();

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        string activator = thread_var();

        /* SYNC: depend on corresponding sync instead of thread variable */
        if (SyncPtr s = dynamic_pointer_cast<Sync>(program[pc]))
          activator = sync_var(step, s->arg);

        formula <<
          assign_var(exec_var(), smtlib::land({stmt_var(), activator})) <<
          eol;
      }

    formula << eol;
  });
}

string SMTLibEncoder::load (Load & l)
{
  string heap = heap_var(step - 1);

  if (l.indirect)
    return smtlib::select(heap, smtlib::select(heap, smtlib::word2hex(l.arg)));
  else
    return smtlib::select(heap, smtlib::word2hex(l.arg));
}

void SMTLibEncoder::encode ()
{
  /* set logic */
  formula << smtlib::set_logic() << eol << eol;

  /* set initial state */
  add_initial_state();
}

/*******************************************************************************
 * SMT-Lib v2.5 Functional Encoder Class
 ******************************************************************************/
SMTLibEncoderFunctional::SMTLibEncoderFunctional (
                                                  const ProgramListPtr p,
                                                  unsigned long b,
                                                  bool e
                                                 ) : SMTLibEncoder(p, b)
{
  preprocess();

  if (e) encode();
}

void SMTLibEncoderFunctional::add_statement_activation ()
{
  if (verbose)
    formula << smtlib::comment_subsection("statement activation");

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

                  val = cond.empty()
                    ? val
                    : smtlib::land({
                        val,
                        /* only activate successor if jump condition failed */
                        prev == pc - 1 && j->arg != pc
                          ? smtlib::lnot(cond)
                          : cond
                      });
                }

              /* add predecessor to the activation */
              expr = smtlib::ite(stmt_var(step - 1, thread, prev), val, expr);
            }

          formula << assign_var(stmt_var(), expr) << eol;
        }

      formula << eol;
    });
}

void SMTLibEncoderFunctional::add_exit_flag ()
{
  /* skip if step == 1 or EXIT isn't called at all */
  if (exit_pcs.empty() || step < 2)
    return;

  if (verbose)
    formula << smtlib::comment_subsection("exit flag");

  declare_exit_var();

  vector<string> args;

  if (step > 2)
    args.push_back(exit_var(step - 1));

  iterate_threads([&] {
    for (const word & exit_pc : exit_pcs[thread])
      args.push_back(exec_var(step - 1, thread, exit_pc));
  });

  formula << assign_var(exit_var(), smtlib::lor(args)) << eol << eol;
}

void SMTLibEncoderFunctional::add_state_update ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state update");

  /* accumulator */
  declare_accu_vars();

  iterate_threads([&] (Program & program) {
    vector<word> & pcs = accu_pcs[thread];
    string expr = accu_var(step - 1, thread);

    // for (const word & _pc : accu_pcs[thread])
    for (auto rit = pcs.rbegin(); rit != pcs.rend(); ++rit)
      expr =
        smtlib::ite(
          exec_var(step, thread, *rit),
          program[*rit]->encode(*this),
          expr);

    formula << assign_var(accu_var(), expr) << eol;
  });

  formula << eol;

  /* CAS memory register */
  declare_mem_vars();

  iterate_threads([&] (Program & program) {
    vector<word> & pcs = mem_pcs[thread];
    string expr = mem_var(step - 1, thread);

    // for (const word & _pc : mem_pcs[thread])
    for (auto rit = pcs.rbegin(); rit != pcs.rend(); ++rit)
      expr =
        smtlib::ite(
          exec_var(step, thread, *rit),
          program[*rit]->encode(*this),
          expr);

    formula << assign_var(mem_var(), expr) << eol;
  });

  formula << eol;

  /* heap */
  declare_heap_var();

  string expr = heap_var(step - 1);

  iterate_threads_reverse([&] (Program & program) {
    vector<word> & pcs = heap_pcs[thread];

    // for (const word & _pc : heap_pcs[thread])
    for (auto rit = pcs.rbegin(); rit != pcs.rend(); ++rit)
      expr =
        smtlib::ite(
          exec_var(step, thread, *rit),
          program[*rit]->encode(*this),
          expr);
  });

  formula << assign_var(heap_var(), expr) << eol;

  formula << eol;
}

void SMTLibEncoderFunctional::add_exit_code ()
{
  if (verbose)
    formula << smtlib::comment_subsection("exit code");

  formula << smtlib::declare_bv_var(exit_code_var, word_size) << eol << eol;

  string exit_code_ite = smtlib::word2hex(0);

  if (step > 1)
    for (unsigned long k = step; k > 0; k--)
      iterate_threads_reverse([&] (Program & program) {
        for (const word & exit_pc : exit_pcs[thread])
          exit_code_ite =
            smtlib::ite(
              exec_var(k, thread, exit_pc),
              program[exit_pc]->encode(*this),
              exit_code_ite);
      });

  formula << assign_var(exit_code_var, exit_code_ite) << eol << eol;
}

void SMTLibEncoderFunctional::preprocess ()
{
  Encoder::preprocess();

  /* initialize state update maps */
  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      program[pc]->encode(*this);
  });
}

/* SMTLibEncoderFunctional::encode (void) *************************************/
void SMTLibEncoderFunctional::encode ()
{
  /* set logic and add common variable declarations */
  SMTLibEncoder::encode();

  for (step = 1; step <= bound; step++)
    {
      if (verbose)
        formula << smtlib::comment_section("step " + to_string(step));

      /* exit flag */
      add_exit_flag();

      /* statement activation */
      add_statement_activation();

      /* thread scheduling */
      add_thread_scheduling();

      /* synchronization constraints */
      add_synchronization_constraints();

      /* statement execution */
      add_statement_execution();

      /* state update */
      add_state_update();
    }

  step--;

  add_exit_code();
}

#define ALTERS_HEAP if (!step) { heap_pcs[thread].push_back(pc); return ""; }

#define ALTERS_ACCU if (!step) { accu_pcs[thread].push_back(pc); return ""; }

/* SMTLibEncoderFunctional::encode (Load &) ***********************************/
string SMTLibEncoderFunctional::encode (Load & l)
{
  ALTERS_ACCU;

  return load(l);
}

/* SMTLibEncoderFunctional::encode (Store &) **********************************/
string SMTLibEncoderFunctional::encode (Store & s)
{
  ALTERS_HEAP;

  string heap = heap_var(step - 1);

  return
    smtlib::store(
      heap,
      s.indirect
        ? smtlib::select(heap, smtlib::word2hex(s.arg))
        : smtlib::word2hex(s.arg),
      accu_var(step - 1, thread));
}

/* SMTLibEncoderFunctional::encode (Add &) ************************************/
string SMTLibEncoderFunctional::encode (Add & a)
{
  ALTERS_ACCU;

  return smtlib::bvadd({accu_var(step - 1, thread), load(a)});
}

/* SMTLibEncoderFunctional::encode (Addi &) ***********************************/
string SMTLibEncoderFunctional::encode (Addi & a)
{
  ALTERS_ACCU;

  return smtlib::bvadd({accu_var(step - 1, thread), smtlib::word2hex(a.arg)});
}

/* SMTLibEncoderFunctional::encode (Sub &) ************************************/
string SMTLibEncoderFunctional::encode (Sub & s)
{
  ALTERS_ACCU;

  return smtlib::bvsub({accu_var(step - 1, thread), load(s)});
}

/* SMTLibEncoderFunctional::encode (Subi &) ***********************************/
string SMTLibEncoderFunctional::encode (Subi & s)
{
  ALTERS_ACCU;

  return smtlib::bvsub({accu_var(step - 1, thread), smtlib::word2hex(s.arg)});
}

/* SMTLibEncoderFunctional::encode (Cmp &) ************************************/
string SMTLibEncoderFunctional::encode (Cmp & c)
{
  ALTERS_ACCU;

  return smtlib::bvsub({accu_var(step - 1, thread), load(c)});
}

/* SMTLibEncoderFunctional::encode (Jmp &) ************************************/
string SMTLibEncoderFunctional::encode (Jmp & j [[maybe_unused]])
{
  return "";
}

/* SMTLibEncoderFunctional::encode (Jz &) *************************************/
string SMTLibEncoderFunctional::encode (Jz & j [[maybe_unused]])
{
  return smtlib::equality({accu_var(step - 1, thread), smtlib::word2hex(0)});
}

/* SMTLibEncoderFunctional::encode (Jnz &) ************************************/
string SMTLibEncoderFunctional::encode (Jnz & j [[maybe_unused]])
{
  return
    smtlib::lnot(
      smtlib::equality({
        accu_var(step - 1, thread),
        smtlib::word2hex(0)}));
}

/* SMTLibEncoderFunctional::encode (Js &) *************************************/
string SMTLibEncoderFunctional::encode (Js & j [[maybe_unused]])
{
  return
      smtlib::equality({
        "#b1",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(step - 1, thread))});
}

/* SMTLibEncoderFunctional::encode (Jns &) ************************************/
string SMTLibEncoderFunctional::encode (Jns & j [[maybe_unused]])
{
  return
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(step - 1, thread))});
}

/* SMTLibEncoderFunctional::encode (Jnzns &) **********************************/
string SMTLibEncoderFunctional::encode (Jnzns & j [[maybe_unused]])
{
  return
    smtlib::land({
      smtlib::lnot(
        smtlib::equality({
          accu_var(step - 1, thread),
          smtlib::word2hex(0)})),
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var(step - 1, thread))})});
}

/* SMTLibEncoderFunctional::encode (Mem &) ************************************/
string SMTLibEncoderFunctional::encode (Mem & m)
{
  if (!step)
    {
      accu_pcs[thread].push_back(pc);
      mem_pcs[thread].push_back(pc);
      return "";
    }

  return load(m);
}

/* SMTLibEncoderFunctional::encode (Cas &) ************************************/
string SMTLibEncoderFunctional::encode (Cas & c)
{
  ALTERS_HEAP;

  string heap = heap_var(step - 1);
  string addr = c.indirect
    ? smtlib::select(heap_var(step - 1), smtlib::word2hex(c.arg))
    : smtlib::word2hex(c.arg);

  return
    smtlib::ite(
      smtlib::equality({
        mem_var(step - 1, thread),
        smtlib::select(heap, addr)}),
      smtlib::store(
        heap,
        addr,
        accu_var(step - 1, thread)),
      heap);
}

/* SMTLibEncoderFunctional::encode (Sync &) ***********************************/
string SMTLibEncoderFunctional::encode (Sync & s [[maybe_unused]])
{
  return "";
}

/* SMTLibEncoderFunctional::encode (Exit &) ***********************************/
string SMTLibEncoderFunctional::encode (Exit & e)
{
  return smtlib::word2hex(e.arg);
}

/*******************************************************************************
 * SMT-Lib v2.5 Relational Encoder Class
 ******************************************************************************/
SMTLibEncoderRelational::SMTLibEncoderRelational (
                                                  const ProgramListPtr p,
                                                  unsigned long b,
                                                  bool e
                                                 ) : SMTLibEncoder(p, b)
{
  if (e) encode();
}

string SMTLibEncoderRelational::imply (string antecedent, string consequent)
{
  return smtlib::assertion(smtlib::implication(antecedent, consequent)) + eol;
}

string SMTLibEncoderRelational::assign_heap (string exp)
{
  return imply(exec_var(), smtlib::equality({heap_var(), exp}));
}

string SMTLibEncoderRelational::assign_accu (string val)
{
  return imply(exec_var(), smtlib::equality({accu_var(), val}));
}

string SMTLibEncoderRelational::assign_mem (string val)
{
  return imply(exec_var(), smtlib::equality({mem_var(), val}));
}

string SMTLibEncoderRelational::preserve_heap ()
{
  return
    imply(
      exec_var(),
      smtlib::equality({heap_var(), heap_var(step - 1)}));
}

string SMTLibEncoderRelational::preserve_accu ()
{
  return
    imply(
      exec_var(),
      smtlib::equality({accu_var(), accu_var(step - 1, thread)}));
}

string SMTLibEncoderRelational::preserve_mem ()
{
  return
    imply(
      exec_var(),
      smtlib::equality({mem_var(), mem_var(step - 1, thread)}));
}

string SMTLibEncoderRelational::activate_next ()
{
  return activate_pc(pc + 1);
}

string SMTLibEncoderRelational::activate_pc (word target)
{
  return imply(exec_var(), stmt_var(step + 1, thread, target));
}

string SMTLibEncoderRelational::activate_jmp (string condition, word target)
{
  word k = step + 1;

  return
    imply(
      exec_var(),
      smtlib::ite(
        condition,
        stmt_var(k, thread, target),
        stmt_var(k, thread, pc + 1)));
}

void SMTLibEncoderRelational::add_exit_code ()
{
  if (verbose)
    formula << smtlib::comment_subsection("exit code");

  formula << smtlib::declare_bv_var(exit_code_var, word_size) << eol << eol;
}

void SMTLibEncoderRelational::add_exit_flag ()
{
  if (step >= bound)
    return;

  if (verbose)
    formula << smtlib::comment_subsection("exit flag forward declaration");

  step++;

  declare_exit_var();

  step--;

  if (step > 1)
    formula << imply(exit_var(), exit_var(step + 1)) << eol;
}

void SMTLibEncoderRelational::add_statement_declaration ()
{
  if (step >= bound)
    return;

  if (verbose)
    formula
      << smtlib::comment_subsection("statement activation forward declaration");

  step++;

  declare_stmt_vars();

  step--;
}

void SMTLibEncoderRelational::add_state_update ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state update");

  declare_accu_vars();
  declare_mem_vars();
  declare_heap_var();

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << (verbose
          ? "; thread " +
            to_string(thread) +
            "@" +
            to_string(pc) +
            ": " +
            program.print(false, pc) +
            eol
          : "")
        << program[pc]->encode(*this)
        << eol;
  });
}

void SMTLibEncoderRelational::add_state_preservation ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state preservation");

  iterate_threads([&] {
    vector<string> args({thread_var()});

    /* collect sync variables related to this thread */
    for (const auto & [id, threads] : sync_pcs)
      if (threads.find(thread) != threads.end())
        args.push_back(sync_var(step, id));

    string condition = smtlib::lnot(smtlib::land(args));

    /* preserver accu */
    formula <<
      imply(
        condition,
        smtlib::equality({accu_var(), accu_var(step - 1, thread)}));

    /* preserve CAS memory register */
    formula <<
      imply(
        condition,
        smtlib::equality({mem_var(), mem_var(step - 1, thread)}));

    formula << eol;
  });
}

void SMTLibEncoderRelational::encode ()
{
  /* set logic and add common variable declarations */
  SMTLibEncoder::encode();

  /* declare exit code variable */
  add_exit_code();

  /* declare 1st step's statement activation variables */
  add_statement_declaration();

  for (step = 1; step <= bound; step++)
    {
      if (verbose)
        formula << smtlib::comment_section("step " + to_string(step));

      /* exit flag */
      add_exit_flag();

      /* thread scheduling */
      add_thread_scheduling();

      /* synchronization constraints */
      add_synchronization_constraints();

      /* statement execution */
      add_statement_execution();

      /* add forward declaration of statement activation variables */
      add_statement_declaration();

      /* encode instructions */
      add_state_update();

      /* preserve thread's state if it wasn't executed */
      add_state_preservation();
    }
}

string SMTLibEncoderRelational::encode (Load & l)
{
  return
    assign_accu(load(l)) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Store & s)
{
  string addr(
    s.indirect
      ? smtlib::select(heap_var(step - 1), smtlib::word2hex(s.arg))
      : smtlib::word2hex(s.arg));

  return
    preserve_accu() +
    preserve_mem() +
    assign_heap(
      smtlib::store(
        heap_var(step - 1),
        addr,
        accu_var(step - 1, thread))) +
    activate_next();
}

string SMTLibEncoderRelational::encode (Add & a)
{
  return
    assign_accu(smtlib::bvadd({accu_var(step - 1, thread), load(a)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Addi & a)
{
  return
    assign_accu(
      smtlib::bvadd({accu_var(step - 1, thread), smtlib::word2hex(a.arg)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Sub & s)
{
  return
    assign_accu(smtlib::bvsub({accu_var(step - 1, thread), load(s)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Subi & s)
{
  return
    assign_accu(
      smtlib::bvsub({accu_var(step - 1, thread), smtlib::word2hex(s.arg)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Cmp & c)
{
  return
    assign_accu(smtlib::bvsub({accu_var(step - 1, thread), load(c)})) +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Jmp & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_pc(j.arg);
}

string SMTLibEncoderRelational::encode (Jz & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::equality({accu_var(), smtlib::word2hex(0)}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Jnz & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::lnot(smtlib::equality({accu_var(), smtlib::word2hex(0)})),
      j.arg);
}

string SMTLibEncoderRelational::encode (Js & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::equality({
        "#b1",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var())}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Jns & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::equality({
        "#b0",
        smtlib::extract(
          to_string(word_size - 1),
          to_string(word_size - 1),
          accu_var())}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Jnzns & j)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_jmp(
      smtlib::land({
        smtlib::lnot(smtlib::equality({accu_var(), smtlib::word2hex(0)})),
        smtlib::equality({
          "#b0",
          smtlib::extract(
            to_string(word_size - 1),
            to_string(word_size - 1),
            accu_var())})}),
      j.arg);
}

string SMTLibEncoderRelational::encode (Mem & m)
{
  return
    assign_accu(load(m)) +
    assign_mem(accu_var()) +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Cas & c)
{
  string heap = heap_var(step - 1);
  string addr = c.indirect
    ? smtlib::select(heap_var(step - 1), smtlib::word2hex(c.arg))
    : smtlib::word2hex(c.arg);

  return
    preserve_accu() +
    preserve_mem() +
    assign_heap(
      smtlib::ite(
        smtlib::equality({
          mem_var(step - 1, thread),
          smtlib::select(heap, addr)}),
        smtlib::store(
          heap,
          addr,
          accu_var(step - 1, thread)),
        heap)) +
    activate_next();
}

string SMTLibEncoderRelational::encode (Sync & s [[maybe_unused]])
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

string SMTLibEncoderRelational::encode (Exit & e)
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    imply(
      exec_var(),
      exit_var(step + 1)) +
    imply(
      exec_var(),
      smtlib::equality({exit_code_var, smtlib::word2hex(e.arg)}));
}
