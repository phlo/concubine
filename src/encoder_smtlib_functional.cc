/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "encoder_smtlib_functional.hh"

#include <cassert>

#include "smtlib.hh"

namespace ConcuBinE::smtlib {

//==============================================================================
// smtlib::Functional
//==============================================================================

//------------------------------------------------------------------------------
// public member functions inherited from ConcuBinE::smtlib::Encoder
//------------------------------------------------------------------------------

// smtlib::Functional::encode --------------------------------------------------

void Functional::encode ()
{
  Encoder::encode();
  define_exit_code();
}

//------------------------------------------------------------------------------
// private member functions
//------------------------------------------------------------------------------

#define DEFINE_STATE(_update, _type, _var) \
  do { \
    update = _update; \
    iterate_programs([this] (const Program & program) \
      { \
        std::string expr = _var(prev, thread); \
        pc = program.size() - 1; \
        for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--) \
          { \
            const Instruction & op = *rit; \
            if (op.type() & _type) \
              expr = ite(exec_var(prev, thread, pc), op.encode(*this), expr); \
          } \
        formula << assign(_var(step, thread), expr) << eol; \
      }); \
    formula << eol; \
  } while (0)

// smtlib::Functional::define_accu ---------------------------------------------

void Functional::define_accu ()
{
  if (verbose)
    formula << accu_comment;

  DEFINE_STATE(Update::accu, Instruction::Type::accu, accu_var);
}

// smtlib::Functional::define_mem ----------------------------------------------

void Functional::define_mem ()
{
  if (verbose)
    formula << mem_comment;

  DEFINE_STATE(Update::mem, Instruction::Type::mem, mem_var);
}

// smtlib::Functional::define_sb_adr -------------------------------------------

void Functional::define_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  DEFINE_STATE(Update::sb_adr, Instruction::Type::write, sb_adr_var);
}

// smtlib::Functional::define_sb_val -------------------------------------------

void Functional::define_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  DEFINE_STATE(Update::sb_val, Instruction::Type::write, sb_val_var);
}

// smtlib::Functional::define_sb_full ------------------------------------------

void Functional::define_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_programs([this] (const Program & program)
    {
      std::vector<std::string> args;
      pc = program.size() - 1;

      for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
        if (rit->type() & Instruction::Type::write)
          args.push_back(exec_var(prev, thread, pc));

      args.push_back(sb_full_var(prev, thread));

      formula <<
        assign(
          sb_full_var(),
            ite(
              flush_var(prev, thread),
              FALSE,
              lor(args))) <<
        eol;
    });

  formula << eol;
}

// smtlib::Functional::define_stmt ---------------------------------------------

void Functional::define_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program)
    {
      for (pc = 0; pc < program.size(); pc++)
        {
          // statement reactivation
          std::string expr =
            land(
              stmt_var(prev, thread, pc),
              lnot(exec_var(prev, thread, pc)));

          const auto & pred = predecessors[thread][pc];

          for (auto rit = pred.rbegin(); rit != pred.rend(); ++rit)
            {
              // predecessor's execution variable
              std::string val = exec_var(prev, thread, *rit);

              // build conjunction of execution variable and jump condition
              const Instruction & pre = program[*rit];

              if (pre.is_jump())
                {
                  const std::string cond = pre.encode(*this);

                  // JMP has no condition and returns an empty std::string
                  if (!cond.empty())
                    val =
                      land(
                        val,
                        // only activate successor if jump condition failed
                        *rit == pc - 1 && pre.arg() != pc
                          ? lnot(cond)
                          : cond);
                }

              // add predecessor to the activation
              expr = ite(stmt_var(prev, thread, *rit), val, expr);
            }

          formula << assign(stmt_var(), expr) << eol;
        }

      formula << eol;
    });
}

// smtlib::Functional::define_block --------------------------------------------

void Functional::define_block ()
{
  if (checkpoints.empty())
    return;

  if (verbose)
    formula << block_comment;

  for (const auto & [c, threads] : checkpoints)
    {
      assert(threads.size() > 1);

      for (const auto & [t, pcs] : threads)
        {
          std::vector<std::string> args;
          args.reserve(pcs.size() + 1);

          for (const word_t p : pcs)
            args.push_back(exec_var(prev, t, p));

          args.push_back(block_var(prev, c, t));

          formula <<
            assign(
              block_var(step, c, t),
              ite(
                check_var(prev, c),
                FALSE,
                lor(args))) <<
            eol;
        }

      formula << eol;
    }
}

// smtlib::Functional::define_halt ---------------------------------------------

void Functional::define_halt ()
{
  if (halts.empty())
    return;

  if (verbose)
    formula << halt_comment;

  iterate_threads([this]
    {
      if (halts.find(thread) != halts.end())
        {
          const auto & pcs = halts[thread];
          std::vector<std::string> args;
          args.reserve(pcs.size() + 1);

          for (const word_t p : pcs)
            args.push_back(exec_var(prev, thread, p));

          args.push_back(halt_var(prev, thread));

          formula << assign(halt_var(), lor(args)) << eol;
        }
      else
        {
          formula << assign(halt_var(), FALSE) << eol;
        }
    });

  formula << eol;
}

// smtlib::Functional::define_heap ---------------------------------------------

void Functional::define_heap ()
{
  if (verbose)
    formula << heap_comment;

  update = Update::heap;

  const std::string heap_prev = heap_var(prev);
  std::string expr = heap_prev;

  iterate_programs_reverse([this, &heap_prev, &expr] (const Program & program)
    {
      pc = program.size() - 1;

      for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
        {
          const Instruction & op = *rit;

          if (op.type() & Instruction::Type::atomic)
            expr = ite(exec_var(prev, thread, pc), op.encode(*this), expr);
        }

      expr =
        ite(
          flush_var(prev, thread),
          store(
            heap_prev,
            sb_adr_var(prev, thread),
            sb_val_var(prev, thread)),
          expr);
    });

  formula << assign(heap_var(), expr) << eol << eol;
}

// smtlib::Functional::define_exit_flag ----------------------------------------

void Functional::define_exit_flag ()
{
  if (halts.empty() && exits.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  std::vector<std::string> args {exit_flag_var(prev)};

  if (!halts.empty())
    {
      std::vector<std::string> halt;
      halt.reserve(num_threads);
      iterate_threads([this, &halt] { halt.push_back(halt_var()); });
      args.push_back(land(halt));
    }

  if (!exits.empty())
    for (const auto & [t, pcs] : exits)
      for (const word_t p : pcs)
        args.push_back(exec_var(prev, t, p));

  formula << assign(exit_flag_var(), lor(args)) << eol << eol;
}

// smtlib::Functional::define_exit_code ----------------------------------------

void Functional::define_exit_code ()
{
  if (verbose)
    formula << comment_section("exit code");

  std::string expr = word2hex(0);

  if (!exits.empty())
    for (size_t k = 0; k <= bound; k++)
      iterate_programs_reverse([this, &expr, k] (const Program & program)
        {
          for (const word_t & exit_pc : exits[thread])
            expr =
              ite(
                exec_var(k, thread, exit_pc),
                program[exit_pc].encode(*this),
                expr);
        });

  formula << assign(exit_code_var, expr) << eol << eol;
}

//------------------------------------------------------------------------------
// private member functions inherited from ConcuBinE::smtlib::Encoder
//------------------------------------------------------------------------------

// smtlib::Functional::define_states -------------------------------------------

void Functional::define_states ()
{
  assert(step);

  if (verbose)
    formula << comment_subsection("state variable definitions");

  define_accu();
  define_mem();
  define_sb_adr();
  define_sb_val();
  define_sb_full();
  define_stmt();
  define_block();
  define_halt();

  define_heap();
  define_exit_flag();
}

} // namespace ConcuBinE::smtlib
