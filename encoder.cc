#include "encoder.hh"

#include <iostream>

#include "btor2.hh"
#include "smtlib.hh"

using namespace std;

/* std::map lookup helper, performing an arbitrary action for missing values */
template <typename K, typename V, typename F>
V & lookup (map<K, V> & m, K k, F fun)
{
  /* avoid extra lookups https://stackoverflow.com/a/101980 */
  auto lb = m.lower_bound(k);

  if (lb != m.end() && !(m.key_comp()(k, lb->first)))
    {
      return lb->second;
    }
  else
    {
      typename map<K, V>::value_type val(k, fun());

      const auto & it = m.insert(lb, val);

      return it->second;
    }
}

/*******************************************************************************
 * Encoder Base Class
 ******************************************************************************/
Encoder::Encoder (const ProgramListPtr p, unsigned long b) :
  programs(p),
  num_threads(p->size()),
  bound(b),
  use_sinz_constraint(num_threads > 4)
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
          exit_pcs[thread].push_back(pc);
      }
  });
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
  step(0)
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

void SMTLibEncoder::declare_exit_code ()
{
  formula << smtlib::declare_bv_var(exit_code_var, word_size) << eol << eol;
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

void SMTLibEncoder::add_exit_flag ()
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
  /* initialize state update maps */
  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const unsigned char attributes = program[pc]->get_attributes();

        if (attributes & Instruction::Attributes::ALTERS_ACCU)
          alters_accu[thread].push_back(pc);

        if (attributes & Instruction::Attributes::ALTERS_MEM)
          alters_mem[thread].push_back(pc);

        if (attributes & Instruction::Attributes::ALTERS_HEAP)
          alters_heap[thread].push_back(pc);
      }
  });

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
                  string cond = j->encode(*this);

                  /* JMP has no condition and returns an empty string */
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

void SMTLibEncoderFunctional::add_state_update ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state update");

  /* accumulator */
  declare_accu_vars();

  update_accu = true;

  iterate_threads([&] (Program & program) {
    vector<word> & pcs = alters_accu[thread];
    string expr = accu_var(step - 1, thread);

    // for (const word & _pc : alters_accu[thread])
    for (auto rit = pcs.rbegin(); rit != pcs.rend(); ++rit)
      expr =
        smtlib::ite(
          exec_var(step, thread, *rit),
          program[*rit]->encode(*this),
          expr);

    formula << assign_var(accu_var(), expr) << eol;
  });

  formula << eol;

  update_accu = false;

  /* CAS memory register */
  declare_mem_vars();

  iterate_threads([&] (Program & program) {
    vector<word> & pcs = alters_mem[thread];
    string expr = mem_var(step - 1, thread);

    // for (const word & _pc : alters_mem[thread])
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
    vector<word> & pcs = alters_heap[thread];

    // for (const word & _pc : alters_heap[thread])
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
    formula << smtlib::comment_section("exit code");

  declare_exit_code();

  string exit_code_ite = smtlib::word2hex(0);

  for (unsigned long k = step; k > 0; k--)
    iterate_threads_reverse([&] (Program & program) {
      for (const word & exit_pc : exit_pcs[thread])
        exit_code_ite =
          smtlib::ite(
            exec_var(k, thread, exit_pc),
            program[exit_pc]->encode(*this),
            exit_code_ite);
    });

  formula << assign_var(exit_code_var, exit_code_ite) << eol;
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

  /* assign exit code */
  add_exit_code();
}

/* SMTLibEncoderFunctional::encode (Load &) ***********************************/
string SMTLibEncoderFunctional::encode (Load & l)
{
  return load(l);
}

/* SMTLibEncoderFunctional::encode (Store &) **********************************/
string SMTLibEncoderFunctional::encode (Store & s)
{
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
  return smtlib::bvadd({accu_var(step - 1, thread), load(a)});
}

/* SMTLibEncoderFunctional::encode (Addi &) ***********************************/
string SMTLibEncoderFunctional::encode (Addi & a)
{
  return smtlib::bvadd({accu_var(step - 1, thread), smtlib::word2hex(a.arg)});
}

/* SMTLibEncoderFunctional::encode (Sub &) ************************************/
string SMTLibEncoderFunctional::encode (Sub & s)
{
  return smtlib::bvsub({accu_var(step - 1, thread), load(s)});
}

/* SMTLibEncoderFunctional::encode (Subi &) ***********************************/
string SMTLibEncoderFunctional::encode (Subi & s)
{
  return smtlib::bvsub({accu_var(step - 1, thread), smtlib::word2hex(s.arg)});
}

/* SMTLibEncoderFunctional::encode (Cmp &) ************************************/
string SMTLibEncoderFunctional::encode (Cmp & c)
{
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
  return load(m);
}

/* SMTLibEncoderFunctional::encode (Cas &) ************************************/
string SMTLibEncoderFunctional::encode (Cas & c)
{
  string heap = heap_var(step - 1);

  string addr = c.indirect
    ? smtlib::select(heap_var(step - 1), smtlib::word2hex(c.arg))
    : smtlib::word2hex(c.arg);

  string condition =
    smtlib::equality({
      mem_var(step - 1, thread),
      smtlib::select(heap, addr)});

  return update_accu
    ? smtlib::ite(
        condition,
        smtlib::word2hex(1),
        smtlib::word2hex(0))
    : smtlib::ite(
        condition,
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

string SMTLibEncoderRelational::stmt_activation (word target)
{
  vector<string> args;

  for (word cur = 0; cur < programs->at(thread - 1u)->size(); cur++)
    args.push_back(
      cur == target
        ? stmt_var(step + 1, thread, target)
        : smtlib::lnot(stmt_var(step + 1, thread, cur)));

  return smtlib::land(args);
}

string SMTLibEncoderRelational::activate_pc (word target)
{
  return step < bound ? imply(exec_var(), stmt_activation(target)) : "";
}

string SMTLibEncoderRelational::activate_next ()
{
  return step < bound ? activate_pc(pc + 1) : "";
}

string SMTLibEncoderRelational::activate_jmp (string condition, word target)
{
  return step < bound
    ? imply(
        exec_var(),
        smtlib::ite(
          condition,
          stmt_activation(target),
          stmt_activation(pc + 1)))
    : "";
}

void SMTLibEncoderRelational::add_exit_code ()
{
  if (verbose)
    formula << smtlib::comment_section("exit code");

  formula <<
    (exit_pcs.empty()
      ? assign_var(exit_code_var, smtlib::word2hex(0)) + eol
      : imply(
          smtlib::lnot(exit_var()),
          smtlib::equality({exit_code_var, smtlib::word2hex(0)})));
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

  if (step == 1)
    add_initial_statement_activation();

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

  iterate_threads([&] (Program & program) {
    vector<string> args({thread_var()});

    /* collect sync variables related to this thread */
    for (const auto & [id, threads] : sync_pcs)
      if (threads.find(thread) != threads.end())
        args.push_back(sync_var(step, id));

    // TODO add condition helper variable wait_<step>_<thread>?
    string condition = smtlib::lnot(smtlib::lor(args));

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

    /* preserver statement activation */
    if (step < bound)
      {
        formula << eol;

        for (pc = 0; pc < program.size(); pc++)
          formula <<
            imply(
              condition,
              smtlib::equality({stmt_var(step + 1, thread, pc), stmt_var()}));
      }

    formula << eol;
  });
}

void SMTLibEncoderRelational::encode ()
{
  /* set logic and add common variable declarations */
  SMTLibEncoder::encode();

  /* declare exit code variable */
  if (verbose)
    formula << "; exit code" << eol;

  declare_exit_code();

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

  step--;

  /* ensure exit code assignment */
  add_exit_code();
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

  string condition =
    smtlib::equality({
      mem_var(step - 1, thread),
      smtlib::select(heap, addr)});

  return
    assign_accu(
      smtlib::ite(
        condition,
        smtlib::word2hex(1),
        smtlib::word2hex(0))) +
    preserve_mem() +
    assign_heap(
      smtlib::ite(
        condition,
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
      smtlib::equality({exit_code_var, smtlib::word2hex(e.arg)}));
}

/*******************************************************************************
 * Btor2 Encoder Class
 ******************************************************************************/
Btor2Encoder::Btor2Encoder (
                            const ProgramListPtr p,
                            unsigned long b,
                            bool e
                           ) : Encoder(p, b), node(1)
{
  /* collect constants */
  nids_const[0] = "";
  nids_const[bound] = "";

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const InstructionPtr & op = program[pc];

        /* collect constants */
        if (UnaryInstructionPtr i = dynamic_pointer_cast<UnaryInstruction>(op))
          nids_const[i->arg] = "";

        /* initialize state update maps */
        const unsigned char attributes = op->get_attributes();

        if (attributes & Instruction::Attributes::ALTERS_ACCU)
          alters_accu[thread].push_back(pc);

        if (attributes & Instruction::Attributes::ALTERS_MEM)
          alters_mem[thread].push_back(pc);

        if (attributes & Instruction::Attributes::ALTERS_HEAP)
          alters_heap[thread].push_back(pc);
      }
  });

  if (e) encode();
}

string Btor2Encoder::nid ()
{
  return to_string(node++);
}

string Btor2Encoder::symbol (word p)
{
  UnaryInstruction & op =
    *dynamic_pointer_cast<UnaryInstruction>(programs->at(thread - 1u)->at(p));

  return
    to_string(thread) +
    ":" +
    to_string(p) +
    ":" +
    op.get_symbol() +
    ":" +
    to_string(op.arg);
}

void Btor2Encoder::declare_sorts ()
{
  if (verbose)
    formula << btor2::comment_section("sorts");

  formula <<
    btor2::declare_sort(sid_bool = nid(), "1") <<
    btor2::declare_sort(sid_bv = nid(), to_string(word_size)) <<
    btor2::declare_array(sid_heap = nid(), "2", "2") <<
    eol;
}

void Btor2Encoder::declare_constants ()
{
  if (verbose)
    formula << btor2::comment_section("constants");

  /* declare boolean constants */
  formula <<
    btor2::constd(nid_false = nid(), sid_bool, "0") <<
    btor2::constd(nid_true = nid(), sid_bool, "1");

  /* declare bitvector constants */
  for (const auto & c : nids_const)
    formula <<
      btor2::constd(
        nids_const[c.first] = nid(),
        sid_bv,
        to_string(c.first));

  formula << eol;
}

void Btor2Encoder::add_bound ()
{
  if (verbose)
    formula << btor2::comment_section("bound");

  /* step counter */
  if (verbose)
    formula << btor2::comment("step counter") << eol;

  string nid_prev;
  string nid_ctr = nid();

  formula <<
    btor2::state(nid_ctr, sid_bv, "k") <<
    btor2::init(nid(), sid_bv, nid_ctr, nids_const[0]) <<
    btor2::add(nid_prev = nid(), sid_bv, nids_const[1], nid_ctr) <<
    btor2::next(nid(), sid_bv, nid_ctr, nid_prev) <<
    eol;

  /* bound */
  if (verbose)
    formula << btor2::comment("bound (" + to_string(bound) + ")") << eol;

  formula <<
    btor2::eq(nid_prev = nid(), sid_bool, nids_const[bound], nid_ctr) <<
    btor2::bad(nid(), nid_prev) <<
    eol;
}

void Btor2Encoder::declare_states ()
{
  if (verbose)
    formula << btor2::comment_section("states");

  /* heap */
  if (verbose)
      formula << btor2::comment("heap") << eol;

  formula << btor2::state(nid_heap = nid(), sid_heap, "heap") << eol;

  /* accumulator */
  if (verbose)
      formula << btor2::comment("accumulator") << eol;

  iterate_threads([&] () {
    formula <<
      btor2::state(
        nids_accu[thread] = nid(),
        sid_bv,
        "accu_" + to_string(thread)) <<
      btor2::init(nid(), sid_bv, nids_accu[thread], nids_const[0]);
  });

  formula << eol;

  /* CAS memory register */
  if (verbose)
      formula << btor2::comment("CAS memory register") << eol;

  iterate_threads([&] () {
    formula <<
      btor2::state(
        nids_mem[thread] = nid(),
        sid_bv,
        "mem_" + to_string(thread)) <<
      btor2::init(nid(), sid_bv, nids_mem[thread], nids_const[0]);
  });

  formula << eol;

  /* statement activation */
  if (verbose)
      formula << btor2::comment("statement activation") << eol;

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula <<
        btor2::state(
          nids_stmt[thread].emplace_back(nid()),
          sid_bool,
          "stmt_" + to_string(thread) + "_" + to_string(pc)) <<
        btor2::init(
          nid(),
          sid_bool,
          nids_stmt[thread].back(),
          pc ? nid_false : nid_true);

    formula << eol;
  });

  /* exit flag */
  if (verbose)
      formula << btor2::comment("exit flag") << eol;

  formula <<
    btor2::state(nid_exit = nid(), sid_bool, "exit") <<
    btor2::init(nid(), sid_bool, nid_exit, nid_false) <<
    eol;

  /* exit code */
  if (verbose)
      formula << btor2::comment("exit code") << eol;

  formula <<
    btor2::state(nid_exit_code = nid(), sid_bv, "exit_code") <<
    btor2::init(nid(), sid_bv, nid_exit_code, nids_const[0]) <<
    eol;
}

void Btor2Encoder::add_thread_scheduling ()
{
  if (verbose)
    formula << btor2::comment_section("thread scheduling");

  /* declare thread inputs */
  iterate_threads([&] () {
    formula <<
      btor2::input(
        nids_thread[thread] = nid(),
        sid_bool,
        "thread_" + to_string(thread));
  });

  formula << eol;

  /* cardinality constraint */
  if (verbose)
    formula << btor2::comment("cardinality constraint") << eol;

  vector<string> variables;

  for (const auto & t : nids_thread)
    variables.push_back(t.second);

  variables.push_back(nid_exit);

  formula <<
    (use_sinz_constraint
      ? btor2::card_constraint_sinz(node, sid_bool, variables)
      : btor2::card_constraint_naive(node, sid_bool, variables)) <<
    eol;
}

void Btor2Encoder::add_synchronization_constraints ()
{
  if (sync_pcs.empty())
    return;

  if (verbose)
    formula << btor2::comment_section("synchronization constraints");

  /* nids of negated thread activation variables */
  map<word, string> nid_not_thread;

  if (verbose)
    formula << btor2::comment("negated thread activation variables") << eol;

  iterate_threads([&] () {
    formula <<
      btor2::lnot(
        nid_not_thread[thread] = nid(),
        sid_bool,
        nids_thread[thread],
        "not_thread_" + to_string(thread));
  });

  formula << eol;

  /* nids of negated synchronization conditions */
  map<word, string> nid_not_sync;

  for (const auto & [id, threads] : sync_pcs)
    {
      if (verbose)
        formula
          << btor2::comment("synchronization condition sync_" + to_string(id))
          << eol;

      /* nids of all synchronization conditions for this barrier */
      vector<string> conditions;

      /* nids of clauses expressing that a specific thread is at this barrier */
      map<word, string> waiting;

      /* generate waiting clauses of each thread containing this barrier */
      for (const auto & [t, pcs] : threads)
        if (pcs.size() > 1)
          {
            vector<string> args;

            for (const auto & p : pcs)
              args.push_back(nids_stmt[t][p]);

            formula <<
              btor2::lor(
                node,
                sid_bool,
                args,
                "thread_" + to_string(t) + "@sync_" + to_string(id));

            waiting[t] = conditions.emplace_back(to_string(node - 1));
          }
        else
          waiting[t] = conditions.emplace_back(nids_stmt[t][*pcs.begin()]);

      /* one of the waiting threads must be executed */
      if (threads.size() != num_threads)
        {
          vector<string> args;

          for (const auto & t : threads)
            args.push_back(nids_thread[t.first]);

          formula << btor2::lor(node, sid_bool, args);

          conditions.push_back(to_string(node - 1));
        }

      /* add synchronization condition sync_<id> */
      if (conditions.size() > 1)
        {
          formula <<
            btor2::land(node, sid_bool, conditions, "sync_" + to_string(id));

          nids_sync[id] = to_string(node - 1);
        }
      else
        {
          nids_sync[id] = conditions.front();
        }

      /* add negated synchronization condition */
      formula <<
        btor2::lnot(
          nid_not_sync[id] = nid(),
          sid_bool,
          nids_sync[id],
          "not_sync_" + to_string(id)) <<
        eol;

      /* disable waiting threads */
      if (verbose)
        formula <<
          btor2::comment(
            "disable threads waiting for barrier " + to_string(id)) <<
          eol;

      for (const auto & t : threads)
        {
          string prev;

          formula <<
            btor2::land(
              prev = nid(),
              sid_bool,
              waiting[t.first],
              nid_not_sync[id]) <<
            btor2::implies(
              nid(),
              sid_bool,
              prev,
              nid_not_thread[t.first]) <<
            btor2::constraint(
              node,
              "sync_" + to_string(id) + "_block_" + to_string(t.first)) <<
            eol;
        }
    }
}

void Btor2Encoder::add_statement_execution ()
{
  if (verbose)
    formula <<
      btor2::comment_section(
        "statement execution - shorthand for statement & thread activation");

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        string activator = nids_thread[thread];

        /* depend on corresponding sync instead of thread variable */
        if (SyncPtr s = dynamic_pointer_cast<Sync>(program[pc]))
          activator = nids_sync[s->arg];

        formula <<
          btor2::land(
            nids_exec[thread].emplace_back(nid()),
            sid_bool,
            nids_stmt[thread][pc],
            activator,
            "exec_" + to_string(thread) + "_" + to_string(pc));
      }

    formula << eol;
  });
}

void Btor2Encoder::add_statement_activation ()
{
  if (verbose)
    formula <<
      btor2::comment_subsection("update statement activation");

  iterate_threads([&] (Program & program) {

    /* map storing nids of jump conditions */
    map<JmpPtr, string> nid_jmp;

    /* reduce lookups */
    const vector<string> & nids_stmt_thread = nids_stmt[thread];
    const vector<string> & nids_exec_thread = nids_exec[thread];

    for (pc = 0; pc < program.size(); pc++)
      {
        if (verbose)
          formula <<
            btor2::comment("stmt_" + to_string(thread) + "_" + to_string(pc)) <<
            eol;

        string nid_next = nid();
        string nid_prev = nids_exec_thread[pc];
        string nid_stmt = nids_stmt_thread[pc];

        /* add statement reactivation */
        formula <<
          btor2::lnot(
            nid_next,
            sid_bool,
            nid_prev) <<
          btor2::land(
            nid_next = nid(),
            sid_bool,
            nid_stmt,
            nid_next);

        /* add activation by predecessor's execution */
        for (word prev : predecessors[thread][pc])
          {
            nid_prev = nids_exec_thread[prev];

            /* predecessor is a jump */
            if (JmpPtr j = dynamic_pointer_cast<Jmp>(program[prev]))
              {
                string nid_cond = lookup(nid_jmp, j, [&] () {
                  return j->encode(*this);
                });

                /* nothing to do here for unconditional jumps (JMP) */
                if (!nid_cond.empty())
                  {
                    /* add negated condition if preceding jump failed */
                    if (prev == pc - 1 && j->arg != pc)
                      formula <<
                        btor2::lnot(
                          nid_cond = nid(),
                          sid_bool,
                          nid_cond);

                    /* add conjunction of execution variable & jump condition */
                    formula <<
                      btor2::land(
                        nid_prev = nid(),
                        sid_bool,
                        nid_prev,
                        nid_cond);
                  }
              }

            /* add predecessors activation */
            formula <<
              btor2::ite(
                nid_next = nid(),
                sid_bool,
                nids_stmt_thread[prev],
                nid_prev,
                nid_next,
                verbose ? symbol(prev) : "");
          }

        formula <<
          btor2::next(
            nid(),
            sid_bool,
            nid_stmt,
            nid_next,
            verbose ? symbol(pc) : "") <<
          eol;
      }
  });
}

void Btor2Encoder::add_state_update (
                                     string nid_state,
                                     string sid,
                                     string sym,
                                     unordered_map<
                                       word,
                                       vector<word>> & alters_state
                                    )
{
  string nid_next = nid_state;

  /* thread == 0 -> global state */
  bool is_global = !thread;

  /* initialize thread to 1 for global state updates */
  if (is_global)
    thread = 1;

  if (verbose && !is_global)
    formula << btor2::comment(sym) << eol;

  unordered_map<word, vector<word>>::iterator thread_it;
  do
    if ((thread_it = alters_state.find(thread)) != alters_state.end())
      {
        /* minimize lookups */
        vector<word> & pcs = thread_it->second;
        vector<string> & exec = nids_exec[thread];

        vector<word>::iterator pc_it = pcs.begin();
        for (pc = *pc_it; pc_it != pcs.end(); ++pc_it, pc = *pc_it)
          {
            UnaryInstruction & op =
              *dynamic_pointer_cast<UnaryInstruction>(
                programs->at(thread - 1u)->at(pc));

            formula <<
              btor2::ite(
                nid_next = nid(),
                sid,
                exec[pc],
                op.encode(*this),
                nid_next,
                verbose ? symbol(pc) : "");
          }
      }
  while (is_global && thread++ < num_threads);

  formula << btor2::next(nid(), sid, nid_state, nid_next) << eol;
}

void Btor2Encoder::add_accu_update ()
{
  if (verbose)
    formula << btor2::comment_subsection("update accu");

  update_accu = true;

  for (thread = 1; thread <= num_threads; thread++)
    add_state_update(
      nids_accu[thread],
      sid_bv,
      "accu_" + to_string(thread),
      alters_accu);

  update_accu = false;
}

void Btor2Encoder::add_mem_update ()
{
  if (verbose)
    formula << btor2::comment_subsection("update CAS memory register");

  for (thread = 1; thread <= num_threads; thread++)
    add_state_update(
      nids_mem[thread],
      sid_bv,
      "mem_" + to_string(thread),
      alters_mem);
}

void Btor2Encoder::add_heap_update ()
{
  if (verbose)
    formula << btor2::comment_subsection("update heap");

  thread = 0; /* global state update */

  add_state_update(nid_heap, sid_heap, "heap", alters_heap);
}

void Btor2Encoder::add_exit_flag_update ()
{
  if (verbose)
    formula << btor2::comment_subsection("update exit flag");

  vector<string> args({nid_exit});

  for (const auto & [t, pcs] : exit_pcs)
    for (const auto & p : pcs)
      args.push_back(nids_exec[t][p]);

  string nid_cond = nid_exit;

  if (args.size() > 1)
    {
      formula << btor2::lor(node, sid_bool, args);
      nid_cond = to_string(node - 1);
    }

  formula << btor2::next(nid(), sid_bool, nid_exit, nid_cond) << eol;
}

void Btor2Encoder::add_exit_code_update ()
{
  if (verbose)
    formula << btor2::comment_subsection("update exit code");

  thread = 0; /* global state update */

  add_state_update(nid_exit_code, sid_bv, "exit_code", exit_pcs);
}

void Btor2Encoder::add_state_update ()
{
  if (verbose)
    formula << btor2::comment_section("state updates");

  /* update statement activation */
  add_statement_activation();

  /* update accu states */
  add_accu_update();

  /* update mem states */
  add_mem_update();

  /* update heap state */
  add_heap_update();

  /* exit flag */
  add_exit_flag_update();

  /* exit code */
  add_exit_code_update();
}

string Btor2Encoder::add_load (string * nid_idx)
{
  formula << btor2::read(*nid_idx = nid(), sid_bv, nid_heap, *nid_idx);

  return *nid_idx;
}

string Btor2Encoder::load (Load & l)
{
  string nid_load = nids_const[l.arg];

  auto add_load = bind(&Btor2Encoder::add_load, this, &nid_load);

  nid_load = lookup(nids_load, l.arg, add_load);

  return l.indirect
    ? lookup(nids_load_indirect, l.arg, add_load)
    : nid_load;
}

/* requires thread to be set */
string Btor2Encoder::store (Store & s)
{
  string nid_store = nids_const[s.arg];

  if (s.indirect)
    nid_store =
      lookup(
        nids_load,
        s.arg,
        bind(&Btor2Encoder::add_load, this, &nid_store));

  map<word, string> & nids_thread_store =
    lookup(
      s.indirect
        ? nids_store_indirect
        : nids_store,
      thread,
      [] () { return map<word, string>(); });

  return
    lookup(
      nids_thread_store,
      s.arg,
      [&] () {
        formula <<
          btor2::write(
            nid_store = nid(),
            sid_heap,
            nid_heap,
            nid_store,
            nids_accu[thread]);

        return nid_store;
      });
}

void Btor2Encoder::encode ()
{
  declare_sorts();
  declare_constants();
  add_bound();
  declare_states();
  add_thread_scheduling();
  add_synchronization_constraints();
  add_statement_execution();
  add_state_update();
}

string Btor2Encoder::encode (Load & l)
{
  return load(l);
}

string Btor2Encoder::encode (Store & s)
{
  return store(s);
}

string Btor2Encoder::encode (Add & a)
{
  string nid_add = load(a);

  formula << btor2::add(nid_add = nid(), sid_bv, nids_accu[thread], nid_add);

  return nid_add;
}

string Btor2Encoder::encode (Addi & a)
{
  string nid_addi = nids_const[a.arg];

  formula << btor2::add(nid_addi = nid(), sid_bv, nids_accu[thread], nid_addi);

  return nid_addi;
}

string Btor2Encoder::encode (Sub & s)
{
  string nid_sub = load(s);

  formula << btor2::sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

string Btor2Encoder::encode (Subi & s)
{
  string nid_subi = nids_const[s.arg];

  formula << btor2::sub(nid_subi = nid(), sid_bv, nids_accu[thread], nid_subi);

  return nid_subi;
}

string Btor2Encoder::encode (Cmp & c)
{
  string nid_sub = load(c);

  formula << btor2::sub(nid_sub = nid(), sid_bv, nids_accu[thread], nid_sub);

  return nid_sub;
}

string Btor2Encoder::encode (Jmp & j [[maybe_unused]])
{
  return "";
}

string Btor2Encoder::encode (Jz & j [[maybe_unused]])
{
  string ret = nid();

  formula << btor2::eq(ret, sid_bool, nids_accu[thread], nids_const[0]);

  return ret;
}

string Btor2Encoder::encode (Jnz & j [[maybe_unused]])
{
  string ret = nid();

  formula << btor2::ne(ret, sid_bool, nids_accu[thread], nids_const[0]);

  return ret;
}

string Btor2Encoder::encode (Js & j [[maybe_unused]])
{
  string msb = to_string(word_size - 1); // TODO: add as static class var?
  string ret = nid();

  formula << btor2::slice(ret, sid_bool, nids_accu[thread], msb, msb);

  return ret;
}

string Btor2Encoder::encode (Jns & j [[maybe_unused]])
{
  string msb = to_string(word_size - 1); // TODO: add as static class var?
  string ret = nid();

  formula <<
    btor2::slice(ret, sid_bool, nids_accu[thread], msb, msb) <<
    btor2::lnot(ret = nid(), sid_bool, ret);

  return ret;
}

string Btor2Encoder::encode (Jnzns & j [[maybe_unused]])
{
  string msb = to_string(word_size - 1); // TODO: add as static class var?

  string nid_nz = nid();

  formula <<
    btor2::ne(nid_nz = nid(), sid_bool, nids_accu[thread], nids_const[0]);

  string nid_nzns = nid();

  formula <<
    btor2::slice(nid_nzns, sid_bool, nids_accu[thread], msb, msb) <<
    btor2::lnot(nid_nzns = nid(), sid_bool, nid_nzns);

  formula <<
    btor2::land(nid_nzns = nid(), sid_bool, nid_nz, nid_nzns);

  return nid_nzns;
}

string Btor2Encoder::encode (Mem & m)
{
  return load(m);
}

string Btor2Encoder::encode (Cas & c)
{
  Load l(c.arg);

  l.indirect = c.indirect;

  string nid_cas = load(l);

  formula << btor2::eq(nid_cas = nid(), sid_bool, nids_mem[thread], nid_cas);

  if (update_accu)
    {
      formula <<
        btor2::ite(
          nid_cas = nid(),
          sid_bv,
          nid_cas,
          nids_const[1],
          nids_const[0]);
    }
  else
    {
      string nid_store = store(c);

      formula <<
        btor2::ite(nid_cas = nid(), sid_heap, nid_cas, nid_store, nid_heap);
    }

  return nid_cas;
}

string Btor2Encoder::encode (Sync & s [[maybe_unused]])
{
  return "";
}

string Btor2Encoder::encode (Exit & e [[maybe_unused]])
{
  return nids_const[e.arg];
}
