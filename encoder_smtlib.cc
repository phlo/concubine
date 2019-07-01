#include "encoder.hh"

#include <cassert>

#include "smtlib.hh"

//==============================================================================
// using declarations
//==============================================================================

using std::string;
using std::to_string;

using std::vector;

using std::runtime_error;

//==============================================================================
// SMTLib_Encoder
//==============================================================================

//------------------------------------------------------------------------------
// static members
//------------------------------------------------------------------------------

// bitvector sort declaration --------------------------------------------------

const string SMTLib_Encoder::bv_sort = smtlib::bitvector(word_size);

// exit code variable ----------------------------------------------------------

const string & SMTLib_Encoder::exit_code_var = exit_code_sym;

// variable comments -----------------------------------------------------------

const string SMTLib_Encoder::accu_comment =
  smtlib::comment(
    Encoder::accu_comment + " - " + accu_sym + "_<step>_<thread>" + eol);

const string SMTLib_Encoder::mem_comment =
  smtlib::comment(
    Encoder::mem_comment + " - " + mem_sym + "_<step>_<thread>" + eol);

const string SMTLib_Encoder::sb_adr_comment =
  smtlib::comment(
    Encoder::sb_adr_comment + " - " + sb_adr_sym + "_<step>_<thread>" + eol);

const string SMTLib_Encoder::sb_val_comment =
  smtlib::comment(
    Encoder::sb_val_comment + " - " + sb_val_sym + "_<step>_<thread>" + eol);

const string SMTLib_Encoder::sb_full_comment =
  smtlib::comment(
    Encoder::sb_full_comment + " - " + sb_full_sym + "_<step>_<thread>" + eol);

const string SMTLib_Encoder::stmt_comment =
  smtlib::comment(
    Encoder::stmt_comment + " - " + stmt_sym + "_<step>_<thread>_<pc>" + eol);

const string SMTLib_Encoder::block_comment =
  smtlib::comment(
    Encoder::block_comment + " - " + block_sym + "_<step>_<id>_<thread>" + eol);

const string SMTLib_Encoder::heap_comment =
  smtlib::comment(
    Encoder::heap_comment + " - " + heap_sym + "_<step>" + eol);

const string SMTLib_Encoder::exit_flag_comment =
  smtlib::comment(
    Encoder::exit_flag_comment + " - " + exit_flag_sym + "_<step>" + eol);

const string SMTLib_Encoder::exit_code_comment =
  smtlib::comment(Encoder::exit_code_comment + eol);

const string SMTLib_Encoder::thread_comment =
  smtlib::comment(
    Encoder::thread_comment + " - " + thread_sym + "_<step>_<thread>" + eol);

const string SMTLib_Encoder::exec_comment =
  smtlib::comment(
    Encoder::exec_comment + " - " + exec_sym + "_<step>_<thread>_<pc>" + eol);

const string SMTLib_Encoder::flush_comment =
  smtlib::comment(
    Encoder::flush_comment + " - " + flush_sym + "_<step>_<thread>" + eol);

const string SMTLib_Encoder::check_comment =
  smtlib::comment(
    Encoder::check_comment + " - " + check_sym + "_<step>_<id>" + eol);

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

SMTLib_Encoder::SMTLib_Encoder (const Program::List::ptr & p, const bound_t b) :
  Encoder(p, b),
  step(0)
{}

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

// SMTLib_Encoder::accu_var ----------------------------------------------------

string SMTLib_Encoder::accu_var (const word_t k, const word_t t)
{
  return accu_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::accu_var () const
{
  return accu_var(step, thread);
}

// SMTLib_Encoder::mem_var -----------------------------------------------------

string SMTLib_Encoder::mem_var (const word_t k, const word_t t)
{
  return mem_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::mem_var () const
{
  return mem_var(step, thread);
}

// SMTLib_Encoder::sb_adr_var --------------------------------------------------

string SMTLib_Encoder::sb_adr_var (const word_t k, const word_t t)
{
  return sb_adr_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::sb_adr_var () const
{
  return sb_adr_var(step, thread);
}

// SMTLib_Encoder::sb_val_var --------------------------------------------------

string SMTLib_Encoder::sb_val_var (const word_t k, const word_t t)
{
  return sb_val_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::sb_val_var () const
{
  return sb_val_var(step, thread);
}

// SMTLib_Encoder::sb_full_var -------------------------------------------------

string SMTLib_Encoder::sb_full_var (const word_t k, const word_t t)
{
  return sb_full_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::sb_full_var () const
{
  return sb_full_var(step, thread);
}

// SMTLib_Encoder::stmt_var ----------------------------------------------------

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

// SMTLib_Encoder::block_var ---------------------------------------------------

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

// SMTLib_Encoder::heap_var ----------------------------------------------------

string SMTLib_Encoder::heap_var (const word_t k)
{
  return heap_sym + '_' + to_string(k);
}

string SMTLib_Encoder::heap_var () const
{
  return heap_var(step);
}

// SMTLib_Encoder::exit_flag_var -----------------------------------------------

string SMTLib_Encoder::exit_flag_var (const word_t k)
{
  return exit_flag_sym + '_' + to_string(k);
}

string SMTLib_Encoder::exit_flag_var () const
{
  return exit_flag_var(step);
}

// SMTLib_Encoder::thread_var --------------------------------------------------

string SMTLib_Encoder::thread_var (const word_t k, const word_t t)
{
  return thread_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::thread_var () const
{
  return thread_var(step, thread);
}

// SMTLib_Encoder::exec_var ----------------------------------------------------

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

// SMTLib_Encoder::flush_var ---------------------------------------------------

string SMTLib_Encoder::flush_var (const word_t k, const word_t t)
{
  return flush_sym + '_' + to_string(k) + '_' + to_string(t);
}

string SMTLib_Encoder::flush_var () const
{
  return flush_var(step, thread);
}

// SMTLib_Encoder::check_var ---------------------------------------------------

string SMTLib_Encoder::check_var (const word_t k, const word_t id)
{
  return check_sym + '_' + to_string(k) + '_' + to_string(id);
}

// SMTLib_Encoder::assign ------------------------------------------------------

string SMTLib_Encoder::assign (string var, string expr)
{
  return smtlib::assertion(smtlib::equality({var, expr}));
}

// SMTLib_Encoder::load --------------------------------------------------------

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
}

// SMTLib_Encoder::declare_accu ------------------------------------------------

void SMTLib_Encoder::declare_accu ()
{
  if (verbose)
    formula << accu_comment;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(accu_var(), word_size) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::declare_mem -------------------------------------------------

void SMTLib_Encoder::declare_mem ()
{
  if (verbose)
    formula << mem_comment;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(mem_var(), word_size) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::declare_sb_adr ----------------------------------------------

void SMTLib_Encoder::declare_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(sb_adr_var(), word_size) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::declare_sb_val ----------------------------------------------

void SMTLib_Encoder::declare_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  iterate_threads([this] {
    formula << smtlib::declare_bv_var(sb_val_var(), word_size) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::declare_sb_full ---------------------------------------------

void SMTLib_Encoder::declare_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(sb_full_var()) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::declare_stmt ------------------------------------------------

void SMTLib_Encoder::declare_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << smtlib::declare_bool_var(stmt_var()) << eol;

    formula << eol;
  });
}

// SMTLib_Encoder::declare_block -----------------------------------------------

void SMTLib_Encoder::declare_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment;

  for (const auto & [s, threads] : check_pcs)
    for (const auto & t : threads)
      formula
        << smtlib::declare_bool_var(block_var(step, s, t.first))
        << eol;

  formula << eol;
}

// SMTLib_Encoder::declare_heap ------------------------------------------------

void SMTLib_Encoder::declare_heap ()
{
  if (verbose)
    formula << heap_comment;

  formula
    << smtlib::declare_array_var(heap_var(), bv_sort, bv_sort)
    << eol << eol;
}

// SMTLib_Encoder::declare_exit_flag -------------------------------------------

void SMTLib_Encoder::declare_exit_flag ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  formula << smtlib::declare_bool_var(exit_flag_var()) << eol << eol;
}

// SMTLib_Encoder::declare_exit_code -------------------------------------------

void SMTLib_Encoder::declare_exit_code ()
{
  if (verbose)
    formula << exit_code_comment;

  formula << smtlib::declare_bv_var(exit_code_var, word_size) << eol << eol;
}

// SMTLib_Encoder::declare_states ----------------------------------------------

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
  declare_exit_flag();

  if (!step)
    declare_exit_code();
}

// SMTLib_Encoder::declare_thread ----------------------------------------------

void SMTLib_Encoder::declare_thread ()
{
  if (verbose)
    formula << thread_comment;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(thread_var()) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::declare_exec ------------------------------------------------

void SMTLib_Encoder::declare_exec ()
{
  if (verbose)
    formula << exec_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << smtlib::declare_bool_var(exec_var()) << eol;

    formula << eol;
  });
}

// SMTLib_Encoder::declare_flush -----------------------------------------------

void SMTLib_Encoder::declare_flush ()
{
  if (verbose)
    formula << flush_comment;

  iterate_threads([this] {
    formula << smtlib::declare_bool_var(flush_var()) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::declare_check -----------------------------------------------

void SMTLib_Encoder::declare_check ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << check_comment;

  for (const auto & s : check_pcs)
    formula << smtlib::declare_bool_var(check_var(step, s.first)) << eol;

  formula << eol;
}

// SMTLib_Encoder::declare_transitions -----------------------------------------

void SMTLib_Encoder::declare_transitions ()
{
  if (verbose)
    formula << smtlib::comment_subsection("transition variable declarations");

  declare_thread();
  declare_exec();
  declare_flush();
  declare_check();
}

// SMTLib_Encoder::init_accu ---------------------------------------------------

#define INIT_STATE(_var) \
  do { \
    iterate_threads([this] { \
      formula << assign(_var(step, thread), smtlib::word2hex(0)) << eol; \
    }); \
    formula << eol; \
  } while (0)

void SMTLib_Encoder::init_accu ()
{
  if (verbose)
    formula << accu_comment;

  INIT_STATE(accu_var);
}

// SMTLib_Encoder::init_mem ----------------------------------------------------

void SMTLib_Encoder::init_mem ()
{
  if (verbose)
    formula << mem_comment;

  INIT_STATE(mem_var);
}

// SMTLib_Encoder::init_sb_adr -------------------------------------------------

void SMTLib_Encoder::init_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  INIT_STATE(sb_adr_var);
}

// SMTLib_Encoder::init_sb_val -------------------------------------------------

void SMTLib_Encoder::init_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  INIT_STATE(sb_val_var);
}

// SMTLib_Encoder::init_sb_full ------------------------------------------------

void SMTLib_Encoder::init_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_threads([this] {
    formula << smtlib::assertion(smtlib::lnot(sb_full_var())) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder::init_stmt ---------------------------------------------------

void SMTLib_Encoder::init_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << smtlib::assertion(pc ? smtlib::lnot(stmt_var()) : stmt_var())
        << eol;

    formula << eol;
  });
}

// SMTLib_Encoder::init_block --------------------------------------------------

void SMTLib_Encoder::init_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment;

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      formula << smtlib::assertion(smtlib::lnot(block_var(step, c, t))) << eol;

  formula << eol;
}

// SMTLib_Encoder::init_exit_flag ----------------------------------------------

void SMTLib_Encoder::init_exit_flag ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  formula << smtlib::assertion(smtlib::lnot(exit_flag_var())) << eol << eol;
}

// SMTLib_Encoder::init_states -------------------------------------------------

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
  init_exit_flag();
}

// SMTLib_Encoder::define_exec -------------------------------------------------

void SMTLib_Encoder::define_exec ()
{
  if (verbose)
    formula << exec_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << assign(exec_var(), smtlib::land({stmt_var(), thread_var()}))
        << eol;

    formula << eol;
  });
}

// SMTLib_Encoder::define_check ------------------------------------------------

void SMTLib_Encoder::define_check ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << check_comment;

  for (const auto & [c, threads] : check_pcs)
    {
      if (step)
        {
          vector<string> check_args;

          check_args.reserve(threads.size());

          for (const auto & t : threads)
            check_args.push_back(block_var(step, c, t.first));

          formula << assign(check_var(step, c), smtlib::land(check_args));
        }
      else
        {
          formula << smtlib::assertion(smtlib::lnot(check_var(step, c)));
        }

      formula << eol;
    }

  formula << eol;
}

// SMTLib_Encoder::define_transitions ------------------------------------------

void SMTLib_Encoder::define_transitions ()
{
  if (verbose)
    formula << smtlib::comment_subsection("transition variable definitions");

  define_exec();
  define_check();
}

// SMTLib_Encoder::define_scheduling_constraints -------------------------------

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
    variables.push_back(exit_flag_var());

  formula
    << (use_sinz_constraint
      ? smtlib::card_constraint_sinz(variables)
      : smtlib::card_constraint_naive(variables))
    << eol;
}

// SMTLib_Encoder::define_store_buffer_constraints -----------------------------

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

// SMTLib_Encoder::define_checkpoint_contraints --------------------------------

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

// SMTLib_Encoder::define_constraints ------------------------------------------

void SMTLib_Encoder::define_constraints ()
{
  define_scheduling_constraints();
  define_store_buffer_constraints();
  define_checkpoint_contraints();
}

// SMTLib_Encoder::encode ------------------------------------------------------

void SMTLib_Encoder::encode ()
{
  formula << smtlib::set_logic() << eol << eol;

  for (step = 0, prev = static_cast<bound_t>(-1); step <= bound; step++, prev++)
    {
      if (verbose)
        formula << smtlib::comment_section("step " + to_string(step));

      declare_states();
      declare_transitions();
      define_transitions();

      if (step)
        define_states();
      else
        init_states();

      define_constraints ();
    }
}

string SMTLib_Encoder::encode (const Instruction::Load & l)
{
  return load(l.arg, l.indirect);
}

string SMTLib_Encoder::encode (const Instruction::Store & s)
{
  switch (update)
    {
    case State::sb_adr:
      return s.indirect ? load(s.arg) : smtlib::word2hex(s.arg);

    case State::sb_val:
      return accu_var(prev, thread);

    default: throw runtime_error("illegal state update");
    }
}

string SMTLib_Encoder::encode (const Instruction::Fence & f [[maybe_unused]])
{
  return "";
}

string SMTLib_Encoder::encode (const Instruction::Add & a)
{
  return smtlib::bvadd({accu_var(prev, thread), load(a.arg, a.indirect)});
}

string SMTLib_Encoder::encode (const Instruction::Addi & a)
{
  return smtlib::bvadd({accu_var(prev, thread), smtlib::word2hex(a.arg)});
}

string SMTLib_Encoder::encode (const Instruction::Sub & s)
{
  return smtlib::bvsub({accu_var(prev, thread), load(s.arg, s.indirect)});
}

string SMTLib_Encoder::encode (const Instruction::Subi & s)
{
  return smtlib::bvsub({accu_var(prev, thread), smtlib::word2hex(s.arg)});
}

string SMTLib_Encoder::encode (const Instruction::Mul & m)
{
  return smtlib::bvmul({accu_var(prev, thread), load(m.arg, m.indirect)});
}

string SMTLib_Encoder::encode (const Instruction::Muli & m)
{
  return smtlib::bvmul({accu_var(prev, thread), smtlib::word2hex(m.arg)});
}

string SMTLib_Encoder::encode (const Instruction::Cmp & c)
{
  return smtlib::bvsub({accu_var(prev, thread), load(c.arg, c.indirect)});
}

string SMTLib_Encoder::encode (const Instruction::Jmp & j [[maybe_unused]])
{
  return "";
}

string SMTLib_Encoder::encode (const Instruction::Jz & j [[maybe_unused]])
{
  return smtlib::equality({accu_var(prev, thread), smtlib::word2hex(0)});
}

string SMTLib_Encoder::encode (const Instruction::Jnz & j [[maybe_unused]])
{
  return
    smtlib::lnot(
      smtlib::equality({
        accu_var(prev, thread),
        smtlib::word2hex(0)}));
}

string SMTLib_Encoder::encode (const Instruction::Js & j [[maybe_unused]])
{
  static const string bw = to_string(word_size - 1);

  return
      smtlib::equality({
        "#b1",
        smtlib::extract(bw, bw, accu_var(prev, thread))});
}

string SMTLib_Encoder::encode (const Instruction::Jns & j [[maybe_unused]])
{
  static const string bw = to_string(word_size - 1);

  return
      smtlib::equality({
        "#b0",
        smtlib::extract(bw, bw, accu_var(prev, thread))});
}

string SMTLib_Encoder::encode (const Instruction::Jnzns & j [[maybe_unused]])
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

string SMTLib_Encoder::encode (const Instruction::Mem & m)
{
  return load(m.arg, m.indirect);
}

string SMTLib_Encoder::encode (const Instruction::Cas & c)
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
    case State::accu:
      return
        smtlib::ite(
          condition,
          smtlib::word2hex(1),
          smtlib::word2hex(0));
    case State::heap:
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

string SMTLib_Encoder::encode (const Instruction::Check & s [[maybe_unused]])
{
  return "";
}

// TODO
string SMTLib_Encoder::encode (const Instruction::Halt & h [[maybe_unused]])
{
  throw runtime_error("not implemented");
}

string SMTLib_Encoder::encode (const Instruction::Exit & e)
{
  return smtlib::word2hex(e.arg);
}
