#include "encoder.hh"

#include <cassert>

#include "smtlib.hh"

//==============================================================================
// using declarations
//==============================================================================

using std::string;
using std::vector;

//==============================================================================
// SMTLib_Encoder_Functional
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

SMTLib_Encoder_Functional::SMTLib_Encoder_Functional (const Program::List::ptr & p,
                                                      const bound_t b,
                                                      const bool e) :
  SMTLib_Encoder(p, b)
{
  if (e) encode();
}

//------------------------------------------------------------------------------
// functions
//------------------------------------------------------------------------------

// SMTLib_Encoder_Functional::define_accu --------------------------------------

#define DEFINE_STATE(_update, _type, _var) \
  do { \
    update = _update; \
    iterate_programs([this] (const Program & program) { \
      string expr = _var(prev, thread); \
      pc = program.size() - 1; \
      for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--) \
        { \
          const Instruction & op = *rit; \
          if (op.type() & _type) \
            expr = \
              smtlib::ite( \
                exec_var(prev, thread, pc), \
                op.encode(*this), \
                expr); \
        } \
      formula << assign(_var(step, thread), expr) << eol; \
    }); \
    formula << eol; \
  } while (0)

void SMTLib_Encoder_Functional::define_accu ()
{
  if (verbose)
    formula << accu_comment;

  DEFINE_STATE(State::accu, Instruction::Type::accu, accu_var);
}

// SMTLib_Encoder_Functional::define_mem ---------------------------------------

void SMTLib_Encoder_Functional::define_mem ()
{
  if (verbose)
    formula << mem_comment;

  DEFINE_STATE(State::mem, Instruction::Type::mem, mem_var);
}

// SMTLib_Encoder_Functional::define_sb_adr ------------------------------------

void SMTLib_Encoder_Functional::define_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment;

  DEFINE_STATE(State::sb_adr, Instruction::Type::write, sb_adr_var);
}

// SMTLib_Encoder_Functional::define_sb_val ------------------------------------

void SMTLib_Encoder_Functional::define_sb_val ()
{
  if (verbose)
    formula << sb_val_comment;

  DEFINE_STATE(State::sb_val, Instruction::Type::write, sb_val_var);
}

// SMTLib_Encoder_Functional::define_sb_full -----------------------------------

void SMTLib_Encoder_Functional::define_sb_full ()
{
  if (verbose)
    formula << sb_full_comment;

  iterate_programs([this] (const Program & program) {
    vector<string> args;
    pc = program.size() - 1;

    for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
      if (rit->type() & Instruction::Type::write)
        args.push_back(exec_var(prev, thread, pc));

    args.push_back(sb_full_var(prev, thread));

    formula <<
      assign(
        sb_full_var(),
          smtlib::ite(
            flush_var(prev, thread),
            smtlib::FALSE,
            smtlib::lor(args))) << eol;
  });

  formula << eol;
}

// SMTLib_Encoder_Functional::define_stmt --------------------------------------

void SMTLib_Encoder_Functional::define_stmt ()
{
  if (verbose)
    formula << stmt_comment;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        // statement reactivation
        string expr =
          smtlib::land({
            stmt_var(prev, thread, pc),
            smtlib::lnot(exec_var(prev, thread, pc))});

        const auto & preds = program.predecessors.at(pc);

        for (auto rit = preds.rbegin(); rit != preds.rend(); ++rit)
          {
            // predecessor's execution variable
            string val = exec_var(prev, thread, *rit);

            // build conjunction of execution variable and jump condition
            const Instruction & pred = program[*rit];

            if (pred.is_jump())
              {
                string cond = pred.encode(*this);

                // JMP has no condition and returns an empty string
                if (!cond.empty())
                  val =
                    smtlib::land({
                      val,
                      // only activate successor if jump condition failed
                      *rit == pc - 1 && pred.arg() != pc
                        ? smtlib::lnot(cond)
                        : cond});
              }

            // add predecessor to the activation
            expr = smtlib::ite(stmt_var(prev, thread, *rit), val, expr);
          }

        formula << assign(stmt_var(), expr) << eol;
      }

    formula << eol;
  });
}

// SMTLib_Encoder_Functional::define_block -------------------------------------

void SMTLib_Encoder_Functional::define_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment;

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      {
        vector<string> block_args;

        block_args.reserve(pcs.size() + 1);

        for (const word_t p : pcs)
          block_args.push_back(exec_var(prev, t, p));

        block_args.push_back(block_var(prev, c, t));

        formula <<
          assign(
            block_var(step, c, t),
            smtlib::ite(
              check_var(prev, c),
              smtlib::FALSE,
              smtlib::lor(block_args))) <<
          eol;
      }

  formula << eol;
}

// SMTLib_Encoder_Functional::define_heap --------------------------------------

void SMTLib_Encoder_Functional::define_heap ()
{
  if (verbose)
    formula << heap_comment;

  update = State::heap;

  const string heap_prev = heap_var(prev);
  string expr = heap_prev;

  iterate_programs_reverse([this, &heap_prev, &expr] (const Program & program) {
    pc = program.size() - 1;

    for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
      {
        const Instruction & op = *rit;

        if (op.type() & Instruction::Type::atomic)
          expr =
            smtlib::ite(
              exec_var(prev, thread, pc),
              op.encode(*this),
              expr);
      }

    expr =
      smtlib::ite(
        flush_var(prev, thread),
        smtlib::store(
          heap_prev,
          sb_adr_var(prev, thread),
          sb_val_var(prev, thread)),
        expr);
  });

  formula << assign(heap_var(), expr) << eol << eol;
}

// SMTLib_Encoder_Functional::define_exit_code ---------------------------------

void SMTLib_Encoder_Functional::define_exit_flag ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_flag_comment;

  vector<string> args {exit_flag_var(prev)};

  iterate_threads([this, &args] {
    for (const word_t & exit_pc : exit_pcs[thread])
      args.push_back(exec_var(prev, thread, exit_pc));
  });

  formula << assign(exit_flag_var(), smtlib::lor(args)) << eol << eol;
}

// SMTLib_Encoder_Functional::define_exit_flag ---------------------------------

void SMTLib_Encoder_Functional::define_exit_code ()
{
  if (verbose)
    formula << smtlib::comment_section("exit code");

  string ite = smtlib::word2hex(0);

  if (!exit_pcs.empty())
    for (bound_t k = step = bound; k > 0; k--)
      iterate_programs_reverse([this, &ite, k] (const Program & program) {
        for (const word_t & exit_pc : exit_pcs[thread])
          ite =
            smtlib::ite(
              exec_var(k, thread, exit_pc),
              program[exit_pc].encode(*this),
              ite);
      });

  formula << assign(exit_code_var, ite) << eol << eol;
}

// SMTLib_Encoder_Functional::define_states ------------------------------------

void SMTLib_Encoder_Functional::define_states ()
{
  assert(step);

  if (verbose)
    formula << smtlib::comment_subsection("state variable definitions");

  define_accu();
  define_mem();
  define_sb_adr();
  define_sb_val();
  define_sb_full();
  define_stmt();
  define_block();

  define_heap();
  define_exit_flag();
}

// SMTLib_Encoder_Functional::encode -------------------------------------------

void SMTLib_Encoder_Functional::encode ()
{
  SMTLib_Encoder::encode();

  define_exit_code();
}
