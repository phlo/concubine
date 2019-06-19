#include "encoder.hh"

#include <cassert>

#include "smtlib.hh"

using namespace std;

const string SMTLib_Encoder::bv_sort = smtlib::bitvector(word_size);

const string SMTLib_Encoder::accu_comment =
  "; accu states - " + accu_sym + "_<step>_<thread>";

const string SMTLib_Encoder::mem_comment =
  "; mem states - " + mem_sym + "_<step>_<thread>";

const string SMTLib_Encoder::sb_adr_comment =
  "; store buffer address states - " + sb_adr_sym + "_<step>_<thread>";

const string SMTLib_Encoder::sb_val_comment =
  "; store buffer value states - " + sb_val_sym + "_<step>_<thread>";

const string SMTLib_Encoder::sb_full_comment =
  "; store buffer full states - " + sb_full_sym + "_<step>_<thread>";

const string SMTLib_Encoder::stmt_comment =
  "; statement activation variables - " + stmt_sym + "_<step>_<thread>_<pc>";

const string SMTLib_Encoder::block_comment =
  "; blocking variables - " + block_sym + "_<step>_<id>_<thread>";

const string SMTLib_Encoder::heap_comment =
  "; heap state - " + heap_sym + "_<step>";

const string SMTLib_Encoder::exit_comment =
  "; exit flag - " + exit_sym + "_<step>";

const string SMTLib_Encoder::thread_comment =
  "; thread activation variables - " + thread_sym + "_<step>_<thread>";

const string SMTLib_Encoder::flush_comment =
  "; store buffer flush variables - " + flush_sym + "_<step>_<thread>";

const string SMTLib_Encoder::check_comment =
  "; checkpoint variables - " + check_sym + "_<step>_<id>";

const string SMTLib_Encoder::exec_comment =
  "; statement execution variables - " + exec_sym + "_<step>_<thread>_<pc>";

const string SMTLib_Encoder::cas_comment =
  "; CAS condition - " + cas_sym + "_<step>_<thread>";

SMTLib_Encoder::SMTLib_Encoder (const Program_list_ptr p, bound_t b) :
  Encoder(p, b),
  step(0)
{}

string SMTLib_Encoder::accu_var (const word_t k, const word_t t)
{
  return accu_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::accu_var () const
{
  return accu_var(step, thread);
}

string SMTLib_Encoder::mem_var (const word_t k, const word_t t)
{
  return mem_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::mem_var () const
{
  return mem_var(step, thread);
}

string SMTLib_Encoder::sb_adr_var (const word_t k, const word_t t)
{
  return sb_adr_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::sb_adr_var () const
{
  return sb_adr_var(step, thread);
}

string SMTLib_Encoder::sb_val_var (const word_t k, const word_t t)
{
  return sb_val_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::sb_val_var () const
{
  return sb_val_var(step, thread);
}

string SMTLib_Encoder::sb_full_var (const word_t k, const word_t t)
{
  return sb_full_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::sb_full_var () const
{
  return sb_full_var(step, thread);
}

string SMTLib_Encoder::stmt_var (const word_t k, const word_t t, const word_t p)
{
  return
    stmt_sym + '_' +
    to_string(k) + '_' +
    to_string(t) + '_' +
    to_string(p);
}

string SMTLib_Encoder::stmt_var () const
{
  return stmt_var(step, thread, pc);
}

string SMTLib_Encoder::block_var (
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

string SMTLib_Encoder::heap_var (const word_t k)
{
  return heap_sym + '_' + to_string(k);
}

string SMTLib_Encoder::heap_var () const
{
  return heap_var(step);
}

string SMTLib_Encoder::exit_var (const word_t k)
{
  return exit_sym + '_' + to_string(k);
}

string SMTLib_Encoder::exit_var () const
{
  return exit_var(step);
}

string SMTLib_Encoder::thread_var (const word_t k, const word_t t)
{
  return thread_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::thread_var () const
{
  return thread_var(step, thread);
}

string SMTLib_Encoder::flush_var (const word_t k, const word_t t)
{
  return flush_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::flush_var () const
{
  return flush_var(step, thread);
}

string SMTLib_Encoder::check_var (const word_t k, const word_t id)
{
  return check_sym + '_' + to_string(k) + '_' + to_string(id);
}

string SMTLib_Encoder::exec_var (const word_t k, const word_t t, const word_t p)
{
  return
    exec_sym + '_' +
    to_string(k) + '_' +
    to_string(t) + '_' +
    to_string(p);
}

string SMTLib_Encoder::exec_var () const
{
  return exec_var(step, thread, pc);
}

/* TODO: really needed?
string SMTLib_Encoder::cas_var (const word_t k, const word_t t)
{
  return cas_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::cas_var () const
{
  return cas_var(step, thread);
}
*/

string SMTLib_Encoder::assign_var (string var, string exp)
{
  return smtlib::assertion(smtlib::equality({var, exp}));
}

string SMTLib_Encoder::load (const word_t adr, const bool indirect)
{
  /*
  (ite sb-full
    (ite (= sb-adr #....)
      sb-val
      (select heap #....))
    (select heap #....))
  */
  /*
  (ite sb-full
    (ite (= sb-adr #....)                   ; sb-full
      (ite (= sb-val #....)                   ; (= sb-adr #....)
        #.... | sb-val                          ; (= sb-val #....)
        (ite (= sb-adr (select heap sb-val))    ; (not (= sb-val #....))
          sb-val                                  ; (= sb-adr (select heap sb-val))
          (select heap (select heap sb-val))))    ; (not (= sb-adr (select heap sb-val)))
      (ite (= sb-adr (select heap #....))     ; (not (= sb-adr #....))
        sb-val                                  ; (= sb-adr (select heap #....))
        (select (select heap #....))))          ; (not (= sb-adr (select heap #....)))
    (select (select heap #x....)))          ; (not sb-full)
  */

  string address = smtlib::word2hex(adr);

  string sb_adr = sb_adr_var(prev, thread);
  string sb_val = sb_val_var(prev, thread);
  string sb_full = sb_full_var(prev, thread);
  string heap = heap_var(prev);

  string select = smtlib::select(heap, address);

  if (indirect)
    {
      string select_sb = smtlib::select(heap, sb_val);
      string select_sb_indirect = smtlib::select(heap, select_sb);
      string select_indirect = smtlib::select(heap, select);

      return
        smtlib::ite(
          sb_full,
          smtlib::ite(
            smtlib::equality({sb_adr, address}),
            smtlib::ite(
              smtlib::equality({sb_val, address}),
              sb_val,
              smtlib::ite(
                smtlib::equality({sb_adr, select_sb}),
                sb_val,
                select_sb_indirect)),
            smtlib::ite(
              smtlib::equality({sb_adr, select}),
              sb_val,
              select_indirect)),
          select_indirect);
    }
  else
    {
      return
        smtlib::ite(
          smtlib::land({sb_full, smtlib::equality({sb_adr, address})}),
          sb_val,
          select);
    }

  /*
  string address = indirect ? load(adr) : smtlib::word2hex(adr);

  return step > 1
    ? smtlib::ite(
        smtlib::land({
          sb_full_var(prev, thread),
          smtlib::equality({sb_adr_var(prev, thread), address})}),
        sb_val_var(prev, thread),
        smtlib::select(heap_var(prev), address))
    : smtlib::select(heap_var(prev), address);
  */
}

void SMTLib_Encoder::declare_accu ()
{
  if (verbose)
    formula << accu_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(accu_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::declare_mem ()
{
  if (verbose)
    formula << mem_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(mem_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::declare_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(sb_adr_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::declare_sb_val ()
{
  if (verbose)
    formula << sb_val_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(sb_val_var(), word_size) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::declare_sb_full ()
{
  if (verbose)
    formula << sb_full_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(sb_full_var()) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::declare_stmt ()
{
  if (verbose)
    formula << stmt_comment << eol;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << smtlib::declare_bool_var(stmt_var()) << eol;

    formula << eol;
  });
}

void SMTLib_Encoder::declare_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment << eol;

  for (const auto & [s, threads] : check_pcs)
    for (const auto & t : threads)
      formula
        << smtlib::declare_bool_var(block_var(step, s, t.first))
        << eol;

  formula << eol;
}

void SMTLib_Encoder::declare_heap ()
{
  if (verbose)
    formula << heap_comment << eol;

  formula
    << smtlib::declare_array_var(heap_var(), bv_sort, bv_sort)
    << eol << eol;
}

void SMTLib_Encoder::declare_exit ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_comment << eol;

  formula << smtlib::declare_bool_var(exit_var()) << eol << eol;
}

void SMTLib_Encoder::declare_exit_code ()
{
  if (verbose)
    formula << smtlib::comment("exit code") << eol;

  formula << smtlib::declare_bv_var(exit_code_sym, word_size) << eol << eol;
}

void SMTLib_Encoder::declare_states ()
{
  if (verbose)
    formula << smtlib::comment_subsection("state variable declarations");

  declare_accu();
  declare_mem();
  declare_sb_adr();
  declare_sb_val();
  declare_sb_full();
  declare_stmt();
  declare_block();

  declare_heap();
  declare_exit();

  if (!step)
    declare_exit_code();
}

void SMTLib_Encoder::declare_thread ()
{
  if (verbose)
    formula << thread_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(thread_var()) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::declare_flush ()
{
  if (verbose)
    formula << flush_comment << eol;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(flush_var()) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::declare_check ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << check_comment << eol;

  for (const auto & s : check_pcs)
    formula << smtlib::declare_bool_var(check_var(step, s.first)) << eol;

  formula << eol;
}

void SMTLib_Encoder::declare_exec ()
{
  if (verbose)
    formula << exec_comment << eol;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << smtlib::declare_bool_var(exec_var()) << eol;

    formula << eol;
  });
}

/* TODO: really needed?
void SMTLib_Encoder::declare_cas_vars ()
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
*/

void SMTLib_Encoder::declare_transitions ()
{
  if (verbose)
    formula << smtlib::comment_subsection("transition variable declarations");

  declare_thread();
  declare_flush();
  declare_check();
  declare_exec();
}

#define INIT_STATE(_var) \
  do { \
    iterate_threads([this] { \
      formula << assign_var(_var(step, thread), smtlib::word2hex(0)) << eol; \
    }); \
    formula << eol; \
  } while (0)

void SMTLib_Encoder::init_accu ()
{
  if (verbose)
    formula << accu_comment << eol;

  INIT_STATE(accu_var);
}

void SMTLib_Encoder::init_mem ()
{
  if (verbose)
    formula << mem_comment << eol;

  INIT_STATE(mem_var);
}

void SMTLib_Encoder::init_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment << eol;

  INIT_STATE(sb_adr_var);
}

void SMTLib_Encoder::init_sb_val ()
{
  if (verbose)
    formula << sb_val_comment << eol;

  INIT_STATE(sb_val_var);
}

void SMTLib_Encoder::init_sb_full ()
{
  if (verbose)
    formula << sb_full_comment << eol;

  iterate_threads([this] {
    formula << smtlib::assertion(smtlib::lnot(sb_full_var())) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder::init_stmt ()
{
  if (verbose)
    formula << stmt_comment << eol;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << smtlib::assertion(pc ? smtlib::lnot(stmt_var()) : stmt_var())
        << eol;

    formula << eol;
  });
}

void SMTLib_Encoder::init_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment << eol;

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      formula << smtlib::assertion(smtlib::lnot(block_var(step, c, t))) << eol;

  formula << eol;
}

void SMTLib_Encoder::init_exit ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_comment << eol;

  formula << smtlib::assertion(smtlib::lnot(exit_var())) << eol << eol;
}

void SMTLib_Encoder::init_states ()
{
  assert(!step);

  if (verbose)
    formula << smtlib::comment_subsection("state variable initializations");

  init_accu();
  init_mem();
  init_sb_adr();
  init_sb_val();
  init_sb_full();
  init_stmt();
  init_block();
  init_exit();
}

void SMTLib_Encoder::define_check ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << check_comment << eol;

  for (const auto & [c, threads] : check_pcs)
    {
      if (step)
        {
          vector<string> check_args;

          check_args.reserve(threads.size());

          for (const auto & t : threads)
            check_args.push_back(block_var(step, c, t.first));

          formula <<
            assign_var(
              check_var(step, c),
              smtlib::land(check_args));
        }
      else
        {
          formula << smtlib::assertion(smtlib::lnot(check_var(step, c)));
        }

      formula << eol;
    }

  formula << eol;
}

void SMTLib_Encoder::define_exec ()
{
  if (verbose)
    formula << exec_comment << eol;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << assign_var(exec_var(), smtlib::land({stmt_var(), thread_var()}))
        << eol;

    formula << eol;
  });
}

void SMTLib_Encoder::define_transitions ()
{
  if (verbose)
    formula << smtlib::comment_subsection("transition variable definitions");

  define_check();
  define_exec();
}

void SMTLib_Encoder::define_store_buffer_constraints ()
{
  if (flush_pcs.empty())
    return;

  if (verbose)
    formula << smtlib::comment_subsection("store buffer constraints");

  iterate_threads([this] {
    if (flush_pcs.find(thread) != flush_pcs.end())
      {
        const auto & pcs = flush_pcs[thread];

        vector<string> stmts;

        stmts.reserve(pcs.size());

        for (const word_t p : pcs)
          stmts.push_back(stmt_var(step, thread, p));

        formula <<
          smtlib::assertion(
            smtlib::ite(
              sb_full_var(),
              smtlib::implication(
                smtlib::lor(stmts),
                smtlib::lnot(thread_var())),
              smtlib::lnot(flush_var()))) <<
          eol;
      }
    else
      {
        // TODO: (or sb-full (not flush)) directly?
        formula <<
          smtlib::assertion(
            smtlib::implication(
              smtlib::lnot(sb_full_var()),
              smtlib::lnot(flush_var()))) <<
          eol;
      }
  });

  formula << eol;
}

void SMTLib_Encoder::define_checkpoint_contraints ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << smtlib::comment_subsection("checkpoint constraints");

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      {
        formula <<
          smtlib::assertion(
            smtlib::implication(
              smtlib::land({
                block_var(step, c, t),
                smtlib::lnot(check_var(step, c))}),
              smtlib::lnot(thread_var(step, t))));

        if (verbose)
          formula << " ; checkpoint " << c << ": thread " << t;

        formula << eol;
      }

  formula << eol;
}

void SMTLib_Encoder::define_scheduling_constraints ()
{
  if (verbose)
    formula << smtlib::comment_subsection("scheduling constraints");

  vector<string> variables;

  variables.reserve(num_threads * 2 + 1);

  iterate_threads([this, &variables] {
    variables.push_back(thread_var());
    variables.push_back(flush_var());
  });

  if (!exit_pcs.empty())
    variables.push_back(exit_var());

  formula
    << (use_sinz_constraint
      ? smtlib::card_constraint_sinz(variables)
      : smtlib::card_constraint_naive(variables))
    << eol;
}

void SMTLib_Encoder::define_constraints ()
{
  define_store_buffer_constraints();
  define_checkpoint_contraints();
  define_scheduling_constraints();
}

void SMTLib_Encoder::encode ()
{
  formula << smtlib::set_logic() << eol << eol;

  for (step = 0, prev = static_cast<bound_t>(-1); step <= bound; step++, prev++)
    {
      if (verbose)
        formula << smtlib::comment_section("step " + to_string(step));

      declare_states();
      declare_transitions();

      if (step)
        define_states();
      else
        init_states();

      define_transitions();

      define_constraints ();
    }
}

string SMTLib_Encoder::encode (Load & l)
{
  return load(l.arg, l.indirect);
}

string SMTLib_Encoder::encode (Store & s)
{
  switch (update)
    {
    case Update::sb_adr:
      return s.indirect ? load(s.arg) : smtlib::word2hex(s.arg);

    case Update::sb_val:
      return accu_var(prev, thread);

    default: throw runtime_error("illegal state update");
    }
}

string SMTLib_Encoder::encode (Fence & f [[maybe_unused]])
{
  return "";
}

string SMTLib_Encoder::encode (Add & a)
{
  return smtlib::bvadd({accu_var(prev, thread), load(a.arg, a.indirect)});
}

string SMTLib_Encoder::encode (Addi & a)
{
  return smtlib::bvadd({accu_var(prev, thread), smtlib::word2hex(a.arg)});
}

string SMTLib_Encoder::encode (Sub & s)
{
  return smtlib::bvsub({accu_var(prev, thread), load(s.arg, s.indirect)});
}

string SMTLib_Encoder::encode (Subi & s)
{
  return smtlib::bvsub({accu_var(prev, thread), smtlib::word2hex(s.arg)});
}

string SMTLib_Encoder::encode (Cmp & c)
{
  return smtlib::bvsub({accu_var(prev, thread), load(c.arg, c.indirect)});
}

string SMTLib_Encoder::encode (Jmp & j [[maybe_unused]])
{
  return "";
}

string SMTLib_Encoder::encode (Jz & j [[maybe_unused]])
{
  return smtlib::equality({accu_var(prev, thread), smtlib::word2hex(0)});
}

string SMTLib_Encoder::encode (Jnz & j [[maybe_unused]])
{
  return
    smtlib::lnot(
      smtlib::equality({
        accu_var(prev, thread),
        smtlib::word2hex(0)}));
}

string SMTLib_Encoder::encode (Js & j [[maybe_unused]])
{
  static const string bw = to_string(word_size - 1);

  return
      smtlib::equality({
        "#b1",
        smtlib::extract(bw, bw, accu_var(prev, thread))});
}

string SMTLib_Encoder::encode (Jns & j [[maybe_unused]])
{
  static const string bw = to_string(word_size - 1);

  return
      smtlib::equality({
        "#b0",
        smtlib::extract(bw, bw, accu_var(prev, thread))});
}

string SMTLib_Encoder::encode (Jnzns & j [[maybe_unused]])
{
  static const string bw = to_string(word_size - 1);

  return
    smtlib::land({
      smtlib::lnot(
        smtlib::equality({
          accu_var(prev, thread),
          smtlib::word2hex(0)})),
      smtlib::equality({
        "#b0",
        smtlib::extract(bw, bw, accu_var(prev, thread))})});
}

string SMTLib_Encoder::encode (Mem & m)
{
  return load(m.arg, m.indirect);
}

string SMTLib_Encoder::encode (Cas & c)
{
  string heap = heap_var(prev);

  string address = c.indirect
    ? smtlib::select(heap, smtlib::word2hex(c.arg))
    : smtlib::word2hex(c.arg);

  string condition =
    smtlib::equality({
      mem_var(prev, thread),
      smtlib::select(heap, address)});

  switch (update)
    {
    case Update::accu:
      return
        smtlib::ite(
          condition,
          smtlib::word2hex(1),
          smtlib::word2hex(0));
    case Update::heap:
      return
        smtlib::ite(
          condition,
          smtlib::store(
            heap,
            address,
            accu_var(prev, thread)),
          heap);
    default: throw runtime_error("illegal state update");
    }
}

string SMTLib_Encoder::encode (Check & s [[maybe_unused]])
{
  return "";
}

// TODO
string SMTLib_Encoder::encode (Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLib_Encoder::encode (Exit & e)
{
  return smtlib::word2hex(e.arg);
}
