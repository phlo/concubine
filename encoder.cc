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
Encoder::Encoder (const Program_list_ptr p, unsigned long b) :
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
            if (program[pc - 1u]->symbol() != "JMP")
              predecessors[thread][pc].insert(pc - 1u);

        if (Jmp_ptr j = dynamic_pointer_cast<Jmp>(program[pc]))
          predecessors[thread][j->arg].insert(pc);

        /* collect CAS statemets */
        if (Cas_ptr c = dynamic_pointer_cast<Cas>(program[pc]))
          cas_threads.insert(thread);

        /* collect CHECK statemets */
        if (Check_ptr s = dynamic_pointer_cast<Check>(program[pc]))
          check_pcs[s->arg][thread].insert(pc);

        /* collect exit calls */
        if (Exit_ptr e = dynamic_pointer_cast<Exit>(program[pc]))
          exit_pcs[thread].push_back(pc);
      }
  });
}

#define ITERATE_THREADS for (thread = 0; thread < num_threads; thread++)

void Encoder::iterate_threads (function<void()> fun)
{
  for (thread = 0; thread < num_threads; thread++)
    fun();
}

void Encoder::iterate_threads (function<void(Program &)> fun)
{
  thread = 0;
  for (const auto & p_ptr : *programs)
    {
      fun(*p_ptr);
      thread++;
    }
}

void Encoder::iterate_threads_reverse (function<void(Program &)> fun)
{
  thread = num_threads - 1;
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

string Encoder::check_pcs_to_string ()
{
  ostringstream ss;

  for (const auto & [id, threads] : check_pcs)
    {
      ss << "check " << id << ": " << eol;
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
SMTLibEncoder::SMTLibEncoder (const Program_list_ptr p, unsigned long b) :
  Encoder(p, b),
  step(0)
{}

/* string constants ***********************************************************/
const string SMTLibEncoder::bv_sort =
  smtlib::bitvector(word_size);

const string SMTLibEncoder::exit_code_var =
  "exit-code";

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

const string SMTLibEncoder::block_comment =
  "; blocking variables - block_<step>_<id>_<thread>";

const string SMTLibEncoder::check_comment =
  "; check variables - check_<step>_<id>";

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

string SMTLibEncoder::block_var (const word k, const word id, const word tid)
{
  return "block_" + to_string(k) + '_' + to_string(id) + '_' + to_string(tid);
}

string SMTLibEncoder::check_var (const word k, const word id)
{
  return "check_" + to_string(k) + '_' + to_string(id);
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

void SMTLibEncoder::declare_block_vars ()
{
  if (verbose)
    formula << block_comment << eol;

  for (const auto & [s, threads] : check_pcs)
    for (const auto & t : threads)
      formula
        << smtlib::declare_bool_var(block_var(step, s, t.first))
        << eol;

  formula << eol;
}

void SMTLibEncoder::declare_check_vars ()
{
  if (verbose)
    formula << check_comment << eol;

  for (const auto & s : check_pcs)
    formula << smtlib::declare_bool_var(check_var(step, s.first)) << eol;

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

void SMTLibEncoder::add_checkpoint_constraints ()
{
  /* skip if step == 1 or CHECK isn't called at all */
  if (check_pcs.empty() || step < 2)
    return;

  if (verbose)
    formula << smtlib::comment_subsection("checkpoint constraints");

  declare_block_vars();

  for (const auto & [s, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      {
        vector<string> block_args;

        block_args.reserve(pcs.size() + 1);

        for (const word p : pcs)
          block_args.push_back(exec_var(step - 1, t, p));

        if (step > 2)
          {
            block_args.push_back(block_var(step - 1, s, t));

            formula <<
              assign_var(
                block_var(step, s, t),
                smtlib::ite(
                  check_var(step - 1, s),
                  "false",
                  smtlib::lor(block_args))) <<
              eol;
          }
        else
          {
            formula <<
              assign_var(
                block_var(step, s, t),
                smtlib::lor(block_args)) <<
              eol;
          }
      }

  formula << eol;

  declare_check_vars();

  for (const auto & [s, threads] : check_pcs)
    {
      vector<string> check_args;

      check_args.reserve(threads.size());

      for (const auto & t : threads)
        check_args.push_back(block_var(step, s, t.first));

      formula <<
        assign_var(
          check_var(step, s),
          smtlib::land(check_args)) <<
        eol;
    }

  formula << eol;

  if (verbose)
    formula << "; prevent scheduling of waiting threads" << eol;

  for (const auto & [s, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      {
        formula <<
          smtlib::assertion(
            smtlib::implication(
              smtlib::land({
                block_var(step, s, t),
                smtlib::lnot(check_var(step, s))}),
              smtlib::lnot(thread_var(step, t))));

        if (verbose)
          formula << " ; checkpoint " << s << ": thread " << t;

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
      formula
        << assign_var(exec_var(), smtlib::land({stmt_var(), thread_var()}))
        << eol;

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
                                                  const Program_list_ptr p,
                                                  unsigned long b,
                                                  bool e
                                                 ) : SMTLibEncoder(p, b)
{
  /* initialize state update maps */
  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const Instruction::Type type = program[pc]->type();

        if (type & Instruction::Types::accu)
          alters_accu[thread].push_back(pc);

        if (type & Instruction::Types::mem)
          alters_mem[thread].push_back(pc);

        if (type & Instruction::Types::write)
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
              if (Jmp_ptr j = dynamic_pointer_cast<Jmp>(program[prev]))
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

      /* checkpoint constraints */
      add_checkpoint_constraints();

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

/* SMTLibEncoderFunctional::encode (Fence &) **********************************/
// TODO
string SMTLibEncoderFunctional::encode (Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
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

/* SMTLibEncoderFunctional::encode (Check &) **********************************/
string SMTLibEncoderFunctional::encode (Check & s [[maybe_unused]])
{
  return "";
}

/* SMTLibEncoderFunctional::encode (Halt &) ***********************************/
// TODO
string SMTLibEncoderFunctional::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
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
                                                  const Program_list_ptr p,
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

  for (word cur = 0; cur < programs->at(thread)->size(); cur++)
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

    /* define waiting variable */
    string preserve = "preserve_" + to_string(step) + "_" + to_string(thread);

    /* waiting condition - thread not scheduled */
    formula
      << smtlib::declare_bool_var(preserve) << eol
      << assign_var(preserve, smtlib::lnot(thread_var())) << eol
      << eol;

    /* preserver accu */
    formula <<
      imply(
        preserve,
        smtlib::equality({accu_var(), accu_var(step - 1, thread)}));

    /* preserve CAS memory register */
    formula <<
      imply(
        preserve,
        smtlib::equality({mem_var(), mem_var(step - 1, thread)}));

    /* preserver statement activation */
    if (step < bound)
      {
        formula << eol;

        for (pc = 0; pc < program.size(); pc++)
          formula <<
            imply(
              preserve,
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

      /* checkpoint constraints */
      add_checkpoint_constraints();

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

// TODO
string SMTLibEncoderRelational::encode (Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
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

string SMTLibEncoderRelational::encode (Check & s [[maybe_unused]])
{
  return
    preserve_accu() +
    preserve_mem() +
    preserve_heap() +
    activate_next();
}

// TODO
string SMTLibEncoderRelational::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
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
string Btor2Encoder::msb = to_string(word_size - 1);

Btor2Encoder::Btor2Encoder (const Program_list_ptr p, unsigned long b, bool e) :
  Encoder(p, b), node(1)
{
  /* collect constants */
  nids_const[0] = "";
  nids_const[bound] = "";

  iterate_threads([&] (Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        const Instruction_ptr & op = program[pc];

        /* collect constants */
        if (Unary_ptr i = dynamic_pointer_cast<Unary>(op))
          nids_const[i->arg] = "";

        /* initialize state update maps */
        const Instruction::Type type = op->type();

        if (type & Instruction::Types::accu)
          alters_accu[thread].push_back(pc);

        if (type & Instruction::Types::mem)
          alters_mem[thread].push_back(pc);

        if (type & Instruction::Types::write)
          alters_heap[thread].push_back(pc);
      }
  });

  if (e) encode();
}

string Btor2Encoder::nid ()
{
  return to_string(node++);
}

string Btor2Encoder::nid (int offset)
{
  return to_string(static_cast<int>(node) + offset);
}

string Btor2Encoder::symbol (word p)
{
  Unary & op = *dynamic_pointer_cast<Unary>(programs->at(thread)->at(p));

  return
    to_string(thread) +
    ":" +
    to_string(p) +
    ":" +
    op.symbol() +
    ":" +
    to_string(op.arg);
}

void Btor2Encoder::declare_heap ()
{
  if (verbose)
    formula << btor2::comment("heap") << eol;

  formula << btor2::state(nid_heap = nid(), sid_heap, "heap") << eol;
}

void Btor2Encoder::declare_accu ()
{
  if (verbose)
    formula << btor2::comment("accumulator registers - accu_<thread>") << eol;

  ITERATE_THREADS
    formula <<
      btor2::state(
        nids_accu[thread] = nid(),
        sid_bv,
        "accu_" + to_string(thread));

  formula << eol;
}

void Btor2Encoder::declare_mem ()
{
  if (verbose)
    formula << btor2::comment("CAS memory registers - mem_<thread>") << eol;

  ITERATE_THREADS
    formula <<
      btor2::state(
        nids_mem[thread] = nid(),
        sid_bv,
        "mem_" + to_string(thread));

  formula << eol;
}

void Btor2Encoder::declare_stmt ()
{
  if (verbose)
    formula
      << btor2::comment("statement activation flags - stmt_<thread>_<pc>")
      << eol;

  ITERATE_THREADS
    {
      auto program_size = (*programs)[thread]->size();

      nids_stmt[thread].reserve(program_size);

      for (pc = 0; pc < program_size; pc++)
        formula <<
          btor2::state(
            nids_stmt[thread].emplace_back(nid()),
            sid_bool,
            "stmt_" + to_string(thread) + "_" + to_string(pc));

      formula << eol;
    }
}

void Btor2Encoder::declare_block ()
{
  if (verbose)
    formula
      << btor2::comment("thread blocking flags - block_<id>_<thread>")
      << eol;

  for (const auto & [s, threads] : check_pcs)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          auto & nids = nids_block.insert(nids_block.end(), {s, {}})->second;

          for (const auto & t : threads)
            formula <<
              btor2::state(
                nids.emplace_hint(nids.end(), t.first, nid())->second,
                sid_bool,
                "block_" + to_string(s) + "_" + to_string(t.first));

          formula << eol;
        }
    }
}

void Btor2Encoder::declare_exit_flag ()
{
  if (verbose)
    formula << btor2::comment("exit flag") << eol;

  formula <<
    btor2::state(nid_exit = nid(), sid_bool, "exit") <<
    eol;
}

void Btor2Encoder::declare_exit_code ()
{
  formula << btor2::state(nid_exit_code = nid(), sid_bv, "exit-code");
}

void Btor2Encoder::define_state (
                                 string nid_state,
                                 string sid,
                                 string nid_init,
                                 string sym,
                                 unordered_map<
                                 word,
                                 vector<word>> & alters_state,
                                 const bool global
                                )
{
  string nid_next = nid_state;

  /* initialize thread for global state updates */
  if (global)
    thread = 0;

  if (verbose && !global)
    formula << btor2::comment(sym) << eol;

  if (!nid_init.empty())
    formula << btor2::init(nid(), sid, nid_state, nid_init);

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
            Unary & op =
              *dynamic_pointer_cast<Unary>(programs->at(thread)->at(pc));

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
  while (global && thread++ < num_threads);

  formula << btor2::next(nid(), sid, nid_state, nid_next, sym) << eol;
}

void Btor2Encoder::define_accu ()
{
  if (verbose)
    formula << btor2::comment_subsection("accumulator definitions");

  update_accu = true;

  ITERATE_THREADS
    {
      define_state(
        nids_accu[thread],
        sid_bv,
        nids_const[0],
        "accu_" + to_string(thread),
        alters_accu);
    }

  update_accu = false;
}

void Btor2Encoder::define_mem ()
{
  if (verbose)
    formula
      << btor2::comment_subsection("CAS memory register definitions");

  ITERATE_THREADS
    {
      define_state(
        nids_mem[thread],
        sid_bv,
        nids_const[0],
        "mem_" + to_string(thread),
        alters_mem);
    }
}

void Btor2Encoder::define_heap ()
{
  define_state(nid_heap, sid_heap, "", "heap", alters_heap, true);
}

void Btor2Encoder::define_stmt ()
{
  iterate_threads([&] (Program & program) {

    /* map storing nids of jump conditions */
    map<Jmp_ptr, string> nid_jmp;

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
        string nid_exec = nids_exec_thread[pc];
        string nid_stmt = nids_stmt_thread[pc];

        /* initialization */
        formula <<
          btor2::init(
            nid_next,
            sid_bool,
            nid_stmt,
            pc ? nid_false : nid_true);

        /* add statement reactivation */
        formula <<
          btor2::land(
            nid_next = nid(),
            sid_bool,
            nid_stmt,
            btor2::lnot(nid_exec));

        /* add activation by predecessor's execution */
        for (word prev : predecessors[thread][pc])
          {
            nid_exec = nids_exec_thread[prev];

            /* predecessor is a jump */
            if (Jmp_ptr j = dynamic_pointer_cast<Jmp>(program[prev]))
              {
                string nid_cond = lookup(nid_jmp, j, [&] () {
                  return j->encode(*this);
                });

                /* nothing to do here for unconditional jumps (JMP) */
                if (!nid_cond.empty())
                  {
                    /* add negated condition if preceding jump failed */
                    if (prev == pc - 1 && j->arg != pc)
                      nid_cond = btor2::lnot(nid_cond);

                    /* add conjunction of execution variable & jump condition */
                    formula <<
                      btor2::land(
                        nid_exec = nid(),
                        sid_bool,
                        nid_exec,
                        nid_cond);
                  }
              }

            /* add predecessors activation */
            formula <<
              btor2::ite(
                nid_next = nid(),
                sid_bool,
                nids_stmt_thread[prev],
                nid_exec,
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

void Btor2Encoder::define_block ()
{
  if (verbose)
    formula << btor2::comment("thread blocking flag definitions") << eol;

  auto nids_check_it = nids_check.begin();
  auto nids_block_it = nids_block.begin();

  for (const auto & [s, threads] : check_pcs)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          string & nid_check = nids_check_it++->second;

          auto nid_block_it = nids_block_it++->second.begin();

          for (const auto & [t, pcs] : threads)
            {
              string prev;
              string sym = "block_" + to_string(s) + '_' + to_string(t);

              string & nid_block = nid_block_it++->second;

              vector<string> args;
              args.reserve(pcs.size() + 1);
              for (const auto & p : pcs)
                args.push_back(nids_exec[t][p]);
              args.push_back(nid_block);

              formula <<
                btor2::init(nid(), sid_bool, nid_block, nid_false) <<
                btor2::lor(node, sid_bool, args) <<
                btor2::ite(
                  prev = nid(),
                  sid_bool,
                  nid_check,
                  nid_false,
                  nid(-1)) <<
                btor2::next(nid(), sid_bool, nid_block, prev, sym) <<
                eol;
            }
        }
    }
}

void Btor2Encoder::define_check ()
{
  if (verbose)
    formula << btor2::comment("checkpoint flags - check_<id>") << eol;

  for (const auto & [s, blocks] : nids_block)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (blocks.size() > 1)
        {
          vector<string> args;

          for (const auto & [t, nid_block] : blocks)
            args.push_back(nid_block);

          formula << btor2::land(node, sid_bool, args, "check_" + to_string(s));

          nids_check.emplace_hint(nids_check.end(), s, nid(-1));
        }
      else
        {
          nids_check.emplace_hint(nids_check.end(), s, blocks.begin()->second);
        }
    }

  formula << eol;
}

void Btor2Encoder::define_exit_flag ()
{
  if (verbose)
    formula << btor2::comment("exit flag") << eol;

  formula << btor2::init(nid(), sid_bool, nid_exit, nid_false);

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

  formula << btor2::next(nid(), sid_bool, nid_exit, nid_cond, "exit") << eol;
}

void Btor2Encoder::define_exit_code ()
{
  if (verbose)
    formula << btor2::comment("exit code") << eol;

  declare_exit_code();

  define_state(
    nid_exit_code,
    sid_bv,
    nids_const[0],
    "exit-code",
    exit_pcs,
    true);
}

void Btor2Encoder::add_sorts ()
{
  if (verbose)
    formula << btor2::comment_section("sorts");

  formula <<
    btor2::declare_sort(sid_bool = nid(), "1") <<
    btor2::declare_sort(sid_bv = nid(), to_string(word_size)) <<
    btor2::declare_array(sid_heap = nid(), "2", "2") <<
    eol;
}

void Btor2Encoder::add_constants ()
{
  if (verbose)
    formula << btor2::comment_section("constants");

  /* declare boolean constants */
  formula <<
    btor2::constd(nid_false = nid(), sid_bool, "0") <<
    btor2::constd(nid_true = nid(), sid_bool, "1") <<
    eol;

  /* declare bitvector constants */
  for (const auto & c : nids_const)
    formula <<
      btor2::constd(
        nids_const[c.first] = nid(),
        sid_bv,
        to_string(c.first));

  formula << eol;
}

void Btor2Encoder::add_machine_state_declarations ()
{
  if (verbose)
    formula << btor2::comment_section("machine state declarations");

  declare_heap();
  declare_accu();
  declare_mem();
  declare_stmt();
  declare_exit_flag();
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

void Btor2Encoder::add_statement_execution ()
{
  if (verbose)
    formula <<
      btor2::comment_section(
        "statement execution - exec_<thread>_<pc>");

  iterate_threads([this] (const Program & program) {

    auto program_size = program.size();

    nids_exec[thread].reserve(program_size);

    for (pc = 0; pc < program_size; pc++)
      {
        string sym = "exec_" + to_string(thread) + '_' + to_string(pc);

        formula <<
          btor2::land(
            nids_exec[thread].emplace_back(nid()),
            sid_bool,
            nids_stmt[thread][pc],
            nids_thread[thread],
            sym);
      }

    formula << eol;
  });
}

void Btor2Encoder::add_statement_activation ()
{
  if (verbose)
    formula <<
      btor2::comment_section("statement activation state definitions");

  define_stmt();
}

void Btor2Encoder::add_register_definitions ()
{
  if (verbose)
    formula << btor2::comment_section("register state definitions");

  define_accu();
  define_mem();
}

void Btor2Encoder::add_heap_definition ()
{
  if (verbose)
    formula << btor2::comment_section("heap state definition");

  define_heap();
}

void Btor2Encoder::add_exit_definitions ()
{
  if (verbose)
    formula << btor2::comment_section("exit state definitions");

  define_exit_flag();
  define_exit_code();
}

void Btor2Encoder::add_checkpoint_constraints ()
{
  /* skip if there is no call to CHECK */
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << btor2::comment_section("checkpoint constraints");

  declare_block();
  define_check();
  define_block();

  if (verbose)
    formula << btor2::comment("prevent scheduling of blocked threads") << eol;

  for (const auto & [s, threads] : nids_block)
    {
      // TODO: ignore single-threaded checkpoints -> see gitlab issue #65
      if (threads.size() > 1)
        {
          string not_check = btor2::lnot(nids_check[s]);

          for (const auto & [t, nid_block] : threads)
            {
              string prev;

              formula <<
                btor2::land(
                  prev = nid(),
                  sid_bool,
                  nid_block,
                  not_check) <<
                btor2::implies(
                  prev = nid(),
                  sid_bool,
                  prev,
                  btor2::lnot(nids_thread[t])) <<
                btor2::constraint(
                  nid(),
                  prev,
                  "block_" + to_string(s) + '_' + to_string(t)) <<
                eol;
            }
        }
    }
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
    btor2::bad(nid(), nid_prev);
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
  add_sorts();
  add_constants();
  add_machine_state_declarations();
  add_thread_scheduling();
  add_statement_execution();
  add_statement_activation();
  add_register_definitions();
  add_heap_definition();
  add_exit_definitions();
  add_checkpoint_constraints();
  add_bound();
}

string Btor2Encoder::encode (Load & l)
{
  return load(l);
}

string Btor2Encoder::encode (Store & s)
{
  return store(s);
}

// TODO
string Btor2Encoder::encode (Fence & f [[maybe_unused]])
{
  throw runtime_error("not implemented");
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
  string ret = nid();

  formula << btor2::slice(ret, sid_bool, nids_accu[thread], msb, msb);

  return ret;
}

string Btor2Encoder::encode (Jns & j [[maybe_unused]])
{
  string ret = nid();

  formula <<
    btor2::slice(ret, sid_bool, nids_accu[thread], msb, msb) <<
    btor2::lnot(ret = nid(), sid_bool, ret);

  return ret;
}

string Btor2Encoder::encode (Jnzns & j [[maybe_unused]])
{
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
  Load l(c.arg, c.indirect);

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

string Btor2Encoder::encode (Check & s [[maybe_unused]])
{
  return "";
}

// TODO
string Btor2Encoder::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string Btor2Encoder::encode (Exit & e [[maybe_unused]])
{
  return nids_const[e.arg];
}
