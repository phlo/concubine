#include "encoder.hh"

#include <cassert>

#include "smtlib.hh"

namespace ConcuBinE::smtlib {

//==============================================================================
// smtlib::Encoder
//==============================================================================

//------------------------------------------------------------------------------
// static members
//------------------------------------------------------------------------------

// bitvector sort declaration --------------------------------------------------

const std::string Encoder::bv_sort = bitvector(word_size);

// exit code variable ----------------------------------------------------------

const std::string & Encoder::exit_code_var = exit_code_sym;

// variable comments -----------------------------------------------------------

const std::string Encoder::accu_comment =
  comment(
    ConcuBinE::Encoder::accu_comment
    + " - "
    + accu_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::mem_comment =
  comment(
    ConcuBinE::Encoder::mem_comment
    + " - "
    + mem_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::sb_adr_comment =
  comment(
    ConcuBinE::Encoder::sb_adr_comment
    + " - "
    + sb_adr_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::sb_val_comment =
  comment(
    ConcuBinE::Encoder::sb_val_comment
    + " - "
    + sb_val_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::sb_full_comment =
  comment(
    ConcuBinE::Encoder::sb_full_comment
    + " - "
    + sb_full_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::stmt_comment =
  comment(
    ConcuBinE::Encoder::stmt_comment
    + " - "
    + stmt_sym
    + "_<step>_<thread>_<pc>"
    + eol);

const std::string Encoder::block_comment =
  comment(
    ConcuBinE::Encoder::block_comment
    + " - "
    + block_sym
    + "_<step>_<id>_<thread>"
    + eol);

const std::string Encoder::halt_comment =
  comment(
    ConcuBinE::Encoder::halt_comment
    + " - "
    + halt_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::heap_comment =
  comment(
    ConcuBinE::Encoder::heap_comment
    + " - "
    + heap_sym
    + "_<step>"
    + eol);

const std::string Encoder::exit_flag_comment =
  comment(
    ConcuBinE::Encoder::exit_flag_comment
    + " - "
    + exit_flag_sym
    + "_<step>"
    + eol);

const std::string Encoder::exit_code_comment =
  comment(ConcuBinE::Encoder::exit_code_comment + eol);

const std::string Encoder::thread_comment =
  comment(
    ConcuBinE::Encoder::thread_comment
    + " - "
    + thread_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::exec_comment =
  comment(
    ConcuBinE::Encoder::exec_comment
    + " - "
    + exec_sym
    + "_<step>_<thread>_<pc>"
    + eol);

const std::string Encoder::flush_comment =
  comment(
    ConcuBinE::Encoder::flush_comment
    + " - "
    + flush_sym
    + "_<step>_<thread>"
    + eol);

const std::string Encoder::check_comment =
  comment(
    ConcuBinE::Encoder::check_comment
    + " - "
    + check_sym
    + "_<step>_<id>"
    + eol);

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

Encoder::Encoder (const Program::List::ptr & p, const size_t b) :
  ConcuBinE::Encoder(p, b),
  step(0)
{}

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

// smtlib::Encoder::accu_var ---------------------------------------------------

std::string Encoder::accu_var (const word_t k, const word_t t)
{
  return accu_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::accu_var () const
{
  return accu_var(step, thread);
}

// smtlib::Encoder::mem_var ----------------------------------------------------

std::string Encoder::mem_var (const word_t k, const word_t t)
{
  return mem_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::mem_var () const
{
  return mem_var(step, thread);
}

// smtlib::Encoder::sb_adr_var -------------------------------------------------

std::string Encoder::sb_adr_var (const word_t k, const word_t t)
{
  return sb_adr_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::sb_adr_var () const
{
  return sb_adr_var(step, thread);
}

// smtlib::Encoder::sb_val_var -------------------------------------------------

std::string Encoder::sb_val_var (const word_t k, const word_t t)
{
  return sb_val_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::sb_val_var () const
{
  return sb_val_var(step, thread);
}

// smtlib::Encoder::sb_full_var ------------------------------------------------

std::string Encoder::sb_full_var (const word_t k, const word_t t)
{
  return sb_full_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::sb_full_var () const
{
  return sb_full_var(step, thread);
}

// smtlib::Encoder::stmt_var ---------------------------------------------------

std::string Encoder::stmt_var (const word_t k, const word_t t, const word_t p)
{
  return
    stmt_sym + '_' +
    std::to_string(k) + '_' +
    std::to_string(t) + '_' +
    std::to_string(p);
}

std::string Encoder::stmt_var () const
{
  return stmt_var(step, thread, pc);
}

// smtlib::Encoder::block_var --------------------------------------------------

std::string Encoder::block_var (const word_t k,
                                const word_t id,
                                const word_t tid)
{
  return
    block_sym + '_' +
    std::to_string(k) + '_' +
    std::to_string(id) + '_' +
    std::to_string(tid);
}

// smtlib::Encoder::halt_var ---------------------------------------------------

std::string Encoder::halt_var (const word_t k, const word_t t)
{
  return halt_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::halt_var () const
{
  return halt_var(step, thread);
}

// smtlib::Encoder::heap_var ---------------------------------------------------

std::string Encoder::heap_var (const word_t k)
{
  return heap_sym + '_' + std::to_string(k);
}

std::string Encoder::heap_var () const
{
  return heap_var(step);
}

// smtlib::Encoder::exit_flag_var ----------------------------------------------

std::string Encoder::exit_flag_var (const word_t k)
{
  return exit_flag_sym + '_' + std::to_string(k);
}

std::string Encoder::exit_flag_var () const
{
  return exit_flag_var(step);
}

// smtlib::Encoder::thread_var -------------------------------------------------

std::string Encoder::thread_var (const word_t k, const word_t t)
{
  return thread_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::thread_var () const
{
  return thread_var(step, thread);
}

// smtlib::Encoder::exec_var ---------------------------------------------------

std::string Encoder::exec_var (const word_t k, const word_t t, const word_t p)
{
  return
    exec_sym + '_' +
    std::to_string(k) + '_' +
    std::to_string(t) + '_' +
    std::to_string(p);
}

std::string Encoder::exec_var () const
{
  return exec_var(step, thread, pc);
}

// smtlib::Encoder::flush_var --------------------------------------------------

std::string Encoder::flush_var (const word_t k, const word_t t)
{
  return flush_sym + '_' + std::to_string(k) + '_' + std::to_string(t);
}

std::string Encoder::flush_var () const
{
  return flush_var(step, thread);
}

// smtlib::Encoder::check_var --------------------------------------------------

std::string Encoder::check_var (const word_t k, const word_t id)
{
  return check_sym + '_' + std::to_string(k) + '_' + std::to_string(id);
}

// smtlib::Encoder::assign -----------------------------------------------------

std::string Encoder::assign (const std::string & var,
                             const std::string & expr) const
{
  return assertion(equality({var, expr}));
}

// smtlib::Encoder::load -------------------------------------------------------

std::string Encoder::load (const word_t adr, const bool indirect)
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

  std::string address = word2hex(adr);

  std::string sb_adr = sb_adr_var(prev, thread);
  std::string sb_val = sb_val_var(prev, thread);
  std::string sb_full = sb_full_var(prev, thread);
  std::string heap = heap_var(prev);

  std::string load = select(heap, address);

  if (indirect)
    {
      std::string load_sb = select(heap, sb_val);
      std::string load_sb_indirect = select(heap, load_sb);
      std::string load_indirect = select(heap, load);

      return
        ite(
          sb_full,
          ite(
            equality({sb_adr, address}),
            ite(
              equality({sb_val, address}),
              sb_val,
              ite(
                equality({sb_adr, load_sb}),
                sb_val,
                load_sb_indirect)),
            ite(
              equality({sb_adr, load}),
              sb_val,
              load_indirect)),
          load_indirect);
    }
  else
    {
      return
        ite(
          land({sb_full, equality({sb_adr, address})}),
          sb_val,
          load);
    }
}

// smtlib::Encoder::declare_accu -----------------------------------------------

void Encoder::declare_accu ()
{
  if (verbose)
    formula << accu_comment;

  iterate_threads([this] {
    formula << declare_bv_var(accu_var(), word_size) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::declare_mem ------------------------------------------------

void Encoder::declare_mem ()
{
  if (verbose)
    formula << mem_comment;

  iterate_threads([this] {
    formula << declare_bv_var(mem_var(), word_size) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::declare_sb_adr ---------------------------------------------

void Encoder::declare_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  iterate_threads([this] {
    formula << declare_bv_var(sb_adr_var(), word_size) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::declare_sb_val ---------------------------------------------

void Encoder::declare_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  iterate_threads([this] {
    formula << declare_bv_var(sb_val_var(), word_size) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::declare_sb_full --------------------------------------------

void Encoder::declare_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_threads([this] {
    formula << declare_bool_var(sb_full_var()) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::declare_stmt -----------------------------------------------

void Encoder::declare_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << declare_bool_var(stmt_var()) << eol;

    formula << eol;
  });
}

// smtlib::Encoder::declare_block ----------------------------------------------

void Encoder::declare_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment;

  for (const auto & [s, threads] : check_pcs)
    for (const auto & t : threads)
      formula
        << declare_bool_var(block_var(step, s, t.first))
        << eol;

  formula << eol;
}

// smtlib::Encoder::declare_halt -----------------------------------------------

void Encoder::declare_halt ()
{
  if (halt_pcs.empty())
    return;

  if (verbose)
    formula << halt_comment;

  for (const auto & it : halt_pcs)
    formula << declare_bool_var(halt_var(step, it.first)) << eol;

  formula << eol;
}

// smtlib::Encoder::declare_heap -----------------------------------------------

void Encoder::declare_heap ()
{
  if (verbose)
    formula << heap_comment;

  formula
    << declare_array_var(heap_var(), bv_sort, bv_sort)
    << eol << eol;
}

// smtlib::Encoder::declare_exit_flag ------------------------------------------

void Encoder::declare_exit_flag ()
{
  if (halt_pcs.empty() && exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  formula << declare_bool_var(exit_flag_var()) << eol << eol;
}

// smtlib::Encoder::declare_exit_code ------------------------------------------

void Encoder::declare_exit_code ()
{
  if (verbose)
    formula << exit_code_comment;

  formula << declare_bv_var(exit_code_var, word_size) << eol << eol;
}

// smtlib::Encoder::declare_states ---------------------------------------------

void Encoder::declare_states ()
{
  if (verbose)
    formula << comment_subsection("state variable declarations");

  declare_accu();
  declare_mem();
  declare_sb_adr();
  declare_sb_val();
  declare_sb_full();
  declare_stmt();
  declare_block();
  declare_halt();

  declare_heap();
  declare_exit_flag();

  if (!step)
    declare_exit_code();
}

// smtlib::Encoder::declare_thread ---------------------------------------------

void Encoder::declare_thread ()
{
  if (verbose)
    formula << thread_comment;

  iterate_threads([this] {
    formula << declare_bool_var(thread_var()) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::declare_exec -----------------------------------------------

void Encoder::declare_exec ()
{
  if (verbose)
    formula << exec_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula << declare_bool_var(exec_var()) << eol;

    formula << eol;
  });
}

// smtlib::Encoder::declare_flush ----------------------------------------------

void Encoder::declare_flush ()
{
  if (verbose)
    formula << flush_comment;

  iterate_threads([this] {
    formula << declare_bool_var(flush_var()) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::declare_check ----------------------------------------------

void Encoder::declare_check ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << check_comment;

  for (const auto & s : check_pcs)
    formula << declare_bool_var(check_var(step, s.first)) << eol;

  formula << eol;
}

// smtlib::Encoder::declare_transitions ----------------------------------------

void Encoder::declare_transitions ()
{
  if (verbose)
    formula << comment_subsection("transition variable declarations");

  declare_thread();
  declare_exec();
  declare_flush();
  declare_check();
}

// smtlib::Encoder::init_accu --------------------------------------------------

#define INIT_STATE(_var) \
  do { \
    iterate_threads([this] { \
      formula << assign(_var(step, thread), word2hex(0)) << eol; \
    }); \
    formula << eol; \
  } while (0)

void Encoder::init_accu ()
{
  if (verbose)
    formula << accu_comment;

  INIT_STATE(accu_var);
}

// smtlib::Encoder::init_mem ---------------------------------------------------

void Encoder::init_mem ()
{
  if (verbose)
    formula << mem_comment;

  INIT_STATE(mem_var);
}

// smtlib::Encoder::init_sb_adr ------------------------------------------------

void Encoder::init_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  INIT_STATE(sb_adr_var);
}

// smtlib::Encoder::init_sb_val ------------------------------------------------

void Encoder::init_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  INIT_STATE(sb_val_var);
}

// smtlib::Encoder::init_sb_full -----------------------------------------------

void Encoder::init_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_threads([this] {
    formula << assertion(lnot(sb_full_var())) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::init_stmt --------------------------------------------------

void Encoder::init_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << assertion(pc ? lnot(stmt_var()) : stmt_var())
        << eol;

    formula << eol;
  });
}

// smtlib::Encoder::init_block -------------------------------------------------

void Encoder::init_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment;

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      formula << assertion(lnot(block_var(step, c, t))) << eol;

  formula << eol;
}

// smtlib::Encoder::init_halt --------------------------------------------------

void Encoder::init_halt ()
{
  if (halt_pcs.empty())
    return;

  if (verbose)
    formula << halt_comment;

  iterate_threads([this] {
    formula << assertion(lnot(halt_var())) << eol;
  });

  formula << eol;
}

// smtlib::Encoder::init_exit_flag ---------------------------------------------

void Encoder::init_exit_flag ()
{
  if (halt_pcs.empty() && exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  formula << assertion(lnot(exit_flag_var())) << eol << eol;
}

// smtlib::Encoder::init_states ------------------------------------------------

void Encoder::init_states ()
{
  assert(!step);

  if (verbose)
    formula << comment_subsection("state variable initializations");

  init_accu();
  init_mem();
  init_sb_adr();
  init_sb_val();
  init_sb_full();
  init_stmt();
  init_block();
  init_halt();
  init_exit_flag();
}

// smtlib::Encoder::define_exec ------------------------------------------------

void Encoder::define_exec ()
{
  if (verbose)
    formula << exec_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      formula
        << assign(exec_var(), land({stmt_var(), thread_var()}))
        << eol;

    formula << eol;
  });
}

// smtlib::Encoder::define_check -----------------------------------------------

void Encoder::define_check ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << check_comment;

  for (const auto & [c, threads] : check_pcs)
    {
      if (step)
        {
          std::vector<std::string> check_args;

          check_args.reserve(threads.size());

          for (const auto & t : threads)
            check_args.push_back(block_var(step, c, t.first));

          formula << assign(check_var(step, c), land(check_args));
        }
      else
        {
          formula << assertion(lnot(check_var(step, c)));
        }

      formula << eol;
    }

  formula << eol;
}

// smtlib::Encoder::define_transitions -----------------------------------------

void Encoder::define_transitions ()
{
  if (verbose)
    formula << comment_subsection("transition variable definitions");

  define_exec();
  define_check();
}

// smtlib::Encoder::define_scheduling_constraints ------------------------------

void Encoder::define_scheduling_constraints ()
{
  if (verbose)
    formula << comment_subsection("scheduling constraints");

  std::vector<std::string> variables;

  variables.reserve(num_threads * 2 + 1);

  iterate_threads([this, &variables] {
    variables.push_back(thread_var());
    variables.push_back(flush_var());
  });

  if (!halt_pcs.empty() || !exit_pcs.empty())
    variables.push_back(exit_flag_var());

  formula
    << (use_sinz_constraint
      ? card_constraint_sinz(variables)
      : card_constraint_naive(variables))
    << eol;
}

// smtlib::Encoder::define_store_buffer_constraints ----------------------------

void Encoder::define_store_buffer_constraints ()
{
  if (verbose)
    formula << comment_subsection("store buffer constraints");

  iterate_threads([this] {
    if (flush_pcs.find(thread) != flush_pcs.end())
      {
        const auto & pcs = flush_pcs[thread];

        std::vector<std::string> stmts;

        stmts.reserve(pcs.size());

        for (const word_t p : pcs)
          stmts.push_back(stmt_var(step, thread, p));

        formula <<
          assertion(
            ite(
              sb_full_var(),
              implication(
                lor(stmts),
                lnot(thread_var())),
              lnot(flush_var()))) <<
          eol;
      }
    else
      {
        // TODO: (or sb-full (not flush)) directly?
        formula <<
          assertion(
            implication(
              lnot(sb_full_var()),
              lnot(flush_var()))) <<
          eol;
      }
  });

  formula << eol;
}

// smtlib::Encoder::define_checkpoint_constraints ------------------------------

void Encoder::define_checkpoint_constraints ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << comment_subsection("checkpoint constraints");

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      {
        formula <<
          assertion(
            implication(
              land({
                block_var(step, c, t),
                lnot(check_var(step, c))}),
              lnot(thread_var(step, t))));

        if (verbose)
          formula << " ; checkpoint " << c << ": thread " << t;

        formula << eol;
      }

  formula << eol;
}

// smtlib::Encoder::define_halt_constraints ------------------------------------

void Encoder::define_halt_constraints ()
{
  if (halt_pcs.empty())
    return;

  if (verbose)
    formula << comment_subsection("halt constraints");

  for (const auto & it : halt_pcs)
    formula <<
      assertion(
        implication(
            halt_var(step, it.first),
            lnot(thread_var(step, it.first)))) <<
      eol;

  formula << eol;
}

// smtlib::Encoder::define_constraints -----------------------------------------

void Encoder::define_constraints ()
{
  define_scheduling_constraints();
  define_store_buffer_constraints();
  define_checkpoint_constraints();
  define_halt_constraints();
}

// smtlib::Encoder::encode -----------------------------------------------------

void Encoder::encode ()
{
  formula << set_logic() << eol << eol;

  for (step = 0, prev = static_cast<size_t>(-1); step <= bound; step++, prev++)
    {
      if (verbose)
        formula << comment_section("step " + std::to_string(step));

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

std::string Encoder::encode (const Instruction::Load & l)
{
  return load(l.arg, l.indirect);
}

std::string Encoder::encode (const Instruction::Store & s)
{
  switch (update)
    {
    case State::sb_adr:
      return s.indirect ? load(s.arg) : word2hex(s.arg);

    case State::sb_val:
      return accu_var(prev, thread);

    default: throw std::runtime_error("illegal state update");
    }
}

std::string Encoder::encode (const Instruction::Fence & f [[maybe_unused]])
{
  return "";
}

std::string Encoder::encode (const Instruction::Add & a)
{
  return bvadd({accu_var(prev, thread), load(a.arg, a.indirect)});
}

std::string Encoder::encode (const Instruction::Addi & a)
{
  return bvadd({accu_var(prev, thread), word2hex(a.arg)});
}

std::string Encoder::encode (const Instruction::Sub & s)
{
  return bvsub({accu_var(prev, thread), load(s.arg, s.indirect)});
}

std::string Encoder::encode (const Instruction::Subi & s)
{
  return bvsub({accu_var(prev, thread), word2hex(s.arg)});
}

std::string Encoder::encode (const Instruction::Mul & m)
{
  return bvmul({accu_var(prev, thread), load(m.arg, m.indirect)});
}

std::string Encoder::encode (const Instruction::Muli & m)
{
  return bvmul({accu_var(prev, thread), word2hex(m.arg)});
}

std::string Encoder::encode (const Instruction::Cmp & c)
{
  return bvsub({accu_var(prev, thread), load(c.arg, c.indirect)});
}

std::string Encoder::encode (const Instruction::Jmp & j [[maybe_unused]])
{
  return "";
}

std::string Encoder::encode (const Instruction::Jz & j [[maybe_unused]])
{
  return equality({accu_var(prev, thread), word2hex(0)});
}

std::string Encoder::encode (const Instruction::Jnz & j [[maybe_unused]])
{
  return
    lnot(
      equality({
        accu_var(prev, thread),
        word2hex(0)}));
}

std::string Encoder::encode (const Instruction::Js & j [[maybe_unused]])
{
  static const std::string bw = std::to_string(word_size - 1);

  return
      equality({
        "#b1",
        extract(bw, bw, accu_var(prev, thread))});
}

std::string Encoder::encode (const Instruction::Jns & j [[maybe_unused]])
{
  static const std::string bw = std::to_string(word_size - 1);

  return
      equality({
        "#b0",
        extract(bw, bw, accu_var(prev, thread))});
}

std::string Encoder::encode (const Instruction::Jnzns & j [[maybe_unused]])
{
  static const std::string bw = std::to_string(word_size - 1);

  return
    land({
      lnot(
        equality({
          accu_var(prev, thread),
          word2hex(0)})),
      equality({
        "#b0",
        extract(bw, bw, accu_var(prev, thread))})});
}

std::string Encoder::encode (const Instruction::Mem & m)
{
  return load(m.arg, m.indirect);
}

std::string Encoder::encode (const Instruction::Cas & c)
{
  std::string heap = heap_var(prev);

  std::string address = c.indirect
    ? select(heap, word2hex(c.arg))
    : word2hex(c.arg);

  std::string condition =
    equality({
      mem_var(prev, thread),
      select(heap, address)});

  switch (update)
    {
    case State::accu:
      return
        ite(
          condition,
          word2hex(1),
          word2hex(0));

    case State::heap:
      return
        ite(
          condition,
          store(
            heap,
            address,
            accu_var(prev, thread)),
          heap);

    default: throw std::runtime_error("illegal state update");
    }
}

std::string Encoder::encode (const Instruction::Check & s [[maybe_unused]])
{
  return "";
}

// TODO
std::string Encoder::encode (const Instruction::Halt & h [[maybe_unused]])
{
  throw std::runtime_error("not implemented");
}

std::string Encoder::encode (const Instruction::Exit & e)
{
  return word2hex(e.arg);
}

} // namespace ConcuBinE::smtlib
