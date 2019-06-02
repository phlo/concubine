#include "encoder.hh"

#include "smtlib.hh"

using namespace std;

const string SMTLibEncoder::bv_sort = smtlib::bitvector(word_size);

const string SMTLibEncoder::accu_comment =
  "; accu states - " + accu_sym + "_<step>_<thread>";

const string SMTLibEncoder::mem_comment =
  "; mem states - " + mem_sym + "_<step>_<thread>";

const string SMTLibEncoder::sb_adr_comment =
  "; store buffer address states - " + sb_adr_sym + "_<step>_<thread>";

const string SMTLibEncoder::sb_val_comment =
  "; store buffer value states - " + sb_val_sym + "_<step>_<thread>";

const string SMTLibEncoder::sb_full_comment =
  "; store buffer full states - " + sb_full_sym + "_<step>_<thread>";

const string SMTLibEncoder::heap_comment =
  "; heap states - " + heap_sym + "_<step>";

const string SMTLibEncoder::thread_comment =
  "; thread activation variables - " + thread_sym + "_<step>_<thread>";

const string SMTLibEncoder::flush_comment =
  "; store buffer flush variables - " + flush_sym + "_<step>_<thread>";

const string SMTLibEncoder::stmt_comment =
  "; statement activation variables - " + stmt_sym + "_<step>_<thread>_<pc>";

const string SMTLibEncoder::exec_comment =
  "; statement execution variables - " + exec_sym + "_<step>_<thread>_<pc>";

const string SMTLibEncoder::cas_comment =
  "; CAS condition - " + cas_sym + "_<step>_<thread>";

const string SMTLibEncoder::block_comment =
  "; blocking variables - " + block_sym + "_<step>_<id>_<thread>";

const string SMTLibEncoder::check_comment =
  "; checkpoint variables - " + check_sym + "_<step>_<id>";

const string SMTLibEncoder::exit_comment =
  "; exit flag - " + exit_sym + "_<step>";

SMTLibEncoder::SMTLibEncoder (const Program_list_ptr p, bound_t b) :
  Encoder(p, b),
  step(0)
{}

string SMTLibEncoder::accu_var (const word_t k, const word_t t)
{
  return accu_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::accu_var () const
{
  return accu_var(step, thread);
}

string SMTLibEncoder::mem_var (const word_t k, const word_t t)
{
  return mem_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::mem_var () const
{
  return mem_var(step, thread);
}

string SMTLibEncoder::sb_adr_var (const word_t k, const word_t t)
{
  return sb_adr_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::sb_adr_var () const
{
  return sb_adr_var(step, thread);
}

string SMTLibEncoder::sb_val_var (const word_t k, const word_t t)
{
  return sb_val_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::sb_val_var () const
{
  return sb_val_var(step, thread);
}

string SMTLibEncoder::sb_full_var (const word_t k, const word_t t)
{
  return sb_full_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::sb_full_var () const
{
  return sb_full_var(step, thread);
}

string SMTLibEncoder::heap_var (const word_t k)
{
  return heap_sym + '_' + to_string(k);
}

string SMTLibEncoder::heap_var () const
{
  return heap_var(step);
}

string SMTLibEncoder::thread_var (const word_t k, const word_t t)
{
  return thread_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::thread_var () const
{
  return thread_var(step, thread);
}

string SMTLibEncoder::flush_var (const word_t k, const word_t t)
{
  return flush_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::flush_var () const
{
  return flush_var(step, thread);
}

string SMTLibEncoder::stmt_var (const word_t k, const word_t t, const word_t p)
{
  return
    stmt_sym + '_' +
    to_string(k) + '_' +
    to_string(t) + '_' +
    to_string(p);
}

string SMTLibEncoder::stmt_var () const
{
  return stmt_var(step, thread, pc);
}

string SMTLibEncoder::exec_var (const word_t k, const word_t t, const word_t p)
{
  return
    exec_sym + '_' +
    to_string(k) + '_' +
    to_string(t) + '_' +
    to_string(p);
}

string SMTLibEncoder::exec_var () const
{
  return exec_var(step, thread, pc);
}

string SMTLibEncoder::cas_var (const word_t k, const word_t t)
{
  return cas_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLibEncoder::cas_var () const
{
  return cas_var(step, thread);
}

string SMTLibEncoder::block_var (
                                 const word_t k,
                                 const word_t id,
                                 const word_t tid
                                )
{
  return
    block_sym + '_' +
    to_string(k) + '_' +
    to_string(id) + '_' +
    to_string(tid);
}

string SMTLibEncoder::check_var (const word_t k, const word_t id)
{
  return check_sym + '_' + to_string(k) + '_' + to_string(id);
}

string SMTLibEncoder::exit_var (const word_t k)
{
  return exit_sym + '_' + to_string(k);
}

string SMTLibEncoder::exit_var () const
{
  return exit_var(step);
}

void SMTLibEncoder::declare_accu_vars ()
{
  if (verbose)
    formula << accu_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(accu_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLibEncoder::declare_mem_vars ()
{
  if (verbose)
    formula << mem_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(mem_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLibEncoder::declare_sb_adr_vars ()
{
  if (verbose)
    formula << sb_adr_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(sb_adr_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLibEncoder::declare_sb_val_vars ()
{
  if (verbose)
    formula << sb_val_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(sb_val_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLibEncoder::declare_sb_full_vars ()
{
  if (verbose)
    formula << sb_full_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(sb_full_var()) << eol;
  });

  formula << eol;
}

void SMTLibEncoder::declare_heap_var ()
{
  if (verbose)
    formula << heap_comment << eol;

  formula
    << smtlib::declare_array_var(heap_var(), bv_sort, bv_sort)
    << eol << eol;
}

void SMTLibEncoder::declare_thread_vars ()
{
  if (verbose)
    formula << thread_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(thread_var()) << eol;
  });
}

void SMTLibEncoder::declare_flush_vars ()
{
  if (verbose)
    formula << flush_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(flush_var()) << eol;
  });
}

void SMTLibEncoder::declare_stmt_vars ()
{
  if (verbose)
    formula << stmt_comment << eol;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << smtlib::declare_bool_var(stmt_var()) << eol;

    formula << eol;
  });
}

void SMTLibEncoder::declare_exec_vars ()
{
  if (verbose)
    formula << exec_comment << eol;

  iterate_programs([this] (const Program & program) {
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

  iterate_threads([this] {
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
  formula << smtlib::declare_bv_var(exit_code_sym, word_size) << eol << eol;
}

string SMTLibEncoder::assign_var (string var, string exp)
{
  return smtlib::assertion(smtlib::equality({var, exp}));
}

void SMTLibEncoder::add_initial_state ()
{
  if (verbose)
    formula << smtlib::comment_section("initial state");

  /* accu */
  declare_accu_vars();

  iterate_threads([this] {
    formula << assign_var(accu_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* CAS memory register */
  declare_mem_vars();

  iterate_threads([this] {
    formula << assign_var(mem_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* store buffer address */
  declare_sb_adr_vars();

  iterate_threads([this] {
    formula << assign_var(sb_adr_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* store buffer value */
  declare_sb_val_vars();

  iterate_threads([this] {
    formula << assign_var(sb_val_var(), smtlib::word2hex(0)) << eol;
  });

  formula << eol;

  /* store buffer full flag */
  declare_sb_full_vars();

  iterate_threads([this] {
    formula << smtlib::assertion(smtlib::lnot(sb_full_var())) << eol;
  });

  formula << eol;

  /* heap */
  declare_heap_var();
}

void SMTLibEncoder::add_initial_statement_activation ()
{
  if (verbose)
    formula << "; initial statement activation" << eol;

  iterate_programs([this] (const Program & program) {
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
    args.push_back(exit_var(prev));

  iterate_threads([this, &args] {
    for (const word_t & exit_pc : exit_pcs[thread])
      args.push_back(exec_var(prev, thread, exit_pc));
  });

  formula << assign_var(exit_var(), smtlib::lor(args)) << eol << eol;
}

void SMTLibEncoder::add_thread_scheduling ()
{
  if (verbose)
    formula << smtlib::comment_subsection("thread scheduling");

  declare_thread_vars();
  formula << eol;

  /* cardinality constraint variables */
  vector<string> variables;

  iterate_threads([this, &variables] {
    variables.push_back(thread_var());
  });

  /* store buffer constraints */
  if (step > 1 && !flush_pcs.empty())
    {
      declare_flush_vars();
      formula << eol;

      if (verbose)
        formula << smtlib::comment("store buffer constraints") << eol;

      iterate_threads([this, &variables] {
        vector<string> stmts;

        if (flush_pcs.find(thread) != flush_pcs.end())
          for (const word_t p : flush_pcs.at(thread))
            stmts.push_back(stmt_var(step, thread, p));

        formula <<
          smtlib::assertion(
            smtlib::ite(
              sb_full_var(prev, thread),
              stmts.empty()
                ? "true"
                : smtlib::implication(
                    smtlib::lor(stmts),
                    smtlib::lnot(thread_var())),
              smtlib::lnot(flush_var()))) <<
          eol;

        variables.push_back(flush_var());
      });

      formula << eol;
    }

  /* add exit flag */
  if (step > 1 && !exit_pcs.empty())
    variables.push_back(exit_var());

  /* cardinality constraint */
  if (verbose)
    formula << smtlib::comment("cardinality constraint") << eol;

  formula
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

        for (const word_t p : pcs)
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

  // TODO: remove
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

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << assign_var(exec_var(), smtlib::land({stmt_var(), thread_var()}))
        << eol;

    formula << eol;
  });
}

string SMTLibEncoder::load (const word_t adr, const bool indirect)
{
  string address = indirect ? load(adr) : smtlib::word2hex(adr);

  return step > 1
    ? smtlib::ite(
        smtlib::land({
          sb_full_var(prev, thread),
          smtlib::equality({sb_adr_var(prev, thread), address})}),
        sb_val_var(prev, thread),
        smtlib::select(heap_var(prev), address))
    : smtlib::select(heap_var(prev), address);
}

void SMTLibEncoder::encode ()
{
  /* set logic */
  formula << smtlib::set_logic() << eol << eol;

  /* set initial state */
  add_initial_state();
}
