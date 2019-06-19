#include "encoder.hh"

#include <cassert>
#include <deque>

#include "smtlib.hh"

using namespace std;

SMTLib_Encoder_Functional::SMTLib_Encoder_Functional (
                                                      const Program_list_ptr p,
                                                      bound_t b,
                                                      bool e
                                                     ) : SMTLib_Encoder(p, b)
{
  if (e) encode();
}

#define DEFINE_STATE(_update, _type, _var) \
  do { \
    update = _update; \
    iterate_programs([this] (const Program & program) { \
      string expr = _var(prev, thread); \
      pc = program.size() - 1; \
      for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--) \
        { \
          const Instruction_ptr & op = *rit; \
          if (op->type() & _type) \
            expr = \
              smtlib::ite( \
                exec_var(prev, thread, pc), \
                op->encode(*this), \
                expr); \
        } \
      formula << assign_var(_var(step, thread), expr) << eol; \
    }); \
    formula << eol; \
  } while (0)

void SMTLib_Encoder_Functional::define_accu ()
{
  if (verbose)
    formula << accu_comment << eol;

  DEFINE_STATE(Update::accu, Types::accu, accu_var);
}

void SMTLib_Encoder_Functional::define_mem ()
{
  if (verbose)
    formula << mem_comment << eol;

  DEFINE_STATE(Update::mem, Types::mem, mem_var);
}

void SMTLib_Encoder_Functional::define_sb_adr ()
{
  if (verbose)
    formula << sb_adr_comment << eol;

  DEFINE_STATE(Update::sb_adr, Types::write, sb_adr_var);
}

void SMTLib_Encoder_Functional::define_sb_val ()
{
  if (verbose)
    formula << sb_val_comment << eol;

  DEFINE_STATE(Update::sb_val, Types::write, sb_val_var);
}

void SMTLib_Encoder_Functional::define_sb_full ()
{
  if (verbose)
    formula << sb_full_comment << eol;

  iterate_programs([this] (const Program & program) {
    vector<string> args;
    pc = program.size() - 1;

    for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
      if ((*rit)->type() & Types::write)
        args.push_back(exec_var(prev, thread, pc));

    args.push_back(sb_full_var(prev, thread));

    formula <<
      assign_var(
        sb_full_var(),
          smtlib::ite(
            flush_var(prev, thread),
            smtlib::FALSE,
            smtlib::lor(args))) << eol;
  });

  formula << eol;
}

void SMTLib_Encoder_Functional::define_stmt ()
{
  if (verbose)
    formula << stmt_comment << eol;

  iterate_programs([this] (const Program & program) {
    for (pc = 0; pc < program.size(); pc++)
      {
        // statement reactivation
        string expr =
          smtlib::land({
            stmt_var(prev, thread, pc),
            smtlib::lnot(exec_var(prev, thread, pc))});

        const auto & pred = program.predecessors.at(pc);

        for (auto p = pred.rbegin(); p != pred.rend(); ++p)
          {
            // predecessor's execution variable
            string val = exec_var(prev, thread, *p);

            // build conjunction of execution variable and jump condition
            if (Jmp_ptr j = dynamic_pointer_cast<Jmp>(program[*p]))
              {
                string cond = j->encode(*this);

                // JMP has no condition and returns an empty string
                if (!cond.empty())
                  val =
                    smtlib::land({
                      val,
                      // only activate successor if jump condition failed
                      *p == pc - 1 && j->arg != pc
                        ? smtlib::lnot(cond)
                        : cond});
              }

            // add predecessor to the activation
            expr = smtlib::ite(stmt_var(prev, thread, *p), val, expr);
          }

        formula << assign_var(stmt_var(), expr) << eol;
      }

    formula << eol;
  });
}

void SMTLib_Encoder_Functional::define_block ()
{
  if (check_pcs.empty())
    return;

  if (verbose)
    formula << block_comment << eol;

  for (const auto & [c, threads] : check_pcs)
    for (const auto & [t, pcs] : threads)
      {
        vector<string> block_args;

        block_args.reserve(pcs.size() + 1);

        for (const word_t p : pcs)
          block_args.push_back(exec_var(prev, t, p));

        block_args.push_back(block_var(prev, c, t));

        formula <<
          assign_var(
            block_var(step, c, t),
            smtlib::ite(
              check_var(prev, c),
              smtlib::FALSE,
              smtlib::lor(block_args))) <<
          eol;
      }

  formula << eol;
}

void SMTLib_Encoder_Functional::define_heap ()
{
  if (verbose)
    formula << heap_comment << eol;

  update = Update::heap;

  const string heap_prev = heap_var(prev);
  string expr = heap_prev;

  iterate_programs_reverse([this, &heap_prev, &expr] (const Program & program) {
    pc = program.size() - 1;

    for (auto rit = program.rbegin(); rit != program.rend(); ++rit, pc--)
      {
        const Instruction_ptr & op = *rit;

        if (op->type() & Types::atomic)
          expr =
            smtlib::ite(
              exec_var(prev, thread, pc),
              op->encode(*this),
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

  formula << assign_var(heap_var(), expr) << eol;

  formula << eol;
}

void SMTLib_Encoder_Functional::define_exit ()
{
  if (exit_pcs.empty())
    return;

  if (verbose)
    formula << exit_comment << eol;

  vector<string> args {exit_var(prev)};

  iterate_threads([this, &args] {
    for (const word_t & exit_pc : exit_pcs[thread])
      args.push_back(exec_var(prev, thread, exit_pc));
  });

  formula << assign_var(exit_var(), smtlib::lor(args)) << eol << eol;
}

// TODO
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
              program[exit_pc]->encode(*this),
              ite);
      });

  formula << assign_var(exit_code_sym, ite) << eol << eol;
}

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
  define_exit();
}

void SMTLib_Encoder_Functional::encode ()
{
  SMTLib_Encoder::encode();

  define_exit_code();
}
