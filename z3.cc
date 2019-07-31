#include "z3.hh"

#include <chrono>
#include <z3++.h>

#include "encoder.hh"

namespace ConcuBinE {

//==============================================================================
// Z3
//==============================================================================

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Z3::name --------------------------------------------------------------------

std::string Z3::name () const { return "z3"; }

// Z3::sat ---------------------------------------------------------------------

bool Z3::sat (const std::string & formula)
{
  using namespace std::chrono;

  z3::context c;
  z3::solver s = c;

  high_resolution_clock::time_point t = high_resolution_clock::now();

  s.from_string(formula.c_str());

  bool sat = s.check() == z3::sat;

  time = duration_cast<milliseconds>(high_resolution_clock::now() - t).count();

  return sat;
}

// Z3::solve -------------------------------------------------------------------

inline
bool eval_bool (z3::context & c, const z3::model & m, const std::string & sym)
{
  return m.eval(c.bool_const(sym.c_str())).is_true();
}

inline
word_t eval_bv (z3::context & c, const z3::model & m, const std::string & sym)
{
  return m.eval(c.bv_const(sym.c_str(), word_size)).get_numeral_uint();
}

inline
word_t eval_array (z3::context & c,
                   const z3::model & m,
                   const std::string & sym,
                   const word_t idx)
{
  return
    m.eval(
      z3::select(
        c.constant(
          sym.c_str(),
          c.array_sort(
            c.bv_sort(word_size),
            c.bv_sort(word_size))),
        c.bv_val(idx, word_size)))
    .get_numeral_uint();
}

Trace::ptr Z3::solve (Encoder & encoder, const std::string & constraints)
{
  using namespace std::chrono;

  z3::context c;
  z3::solver s = c;

  high_resolution_clock::time_point t = high_resolution_clock::now();

  s.from_string(build_formula(encoder, constraints).c_str());

  if (s.check() != z3::sat)
    throw std::runtime_error("formula is not sat");

  z3::model m = s.get_model();

  time = duration_cast<milliseconds>(high_resolution_clock::now() - t).count();

  Trace::ptr trace = std::make_unique<Trace>(encoder.programs);

  for (size_t step = 0; step <= encoder.bound; step++)
    {
      // heap state
      if (step)
        {
          word_t thread = trace->thread();

          if (trace->flush(step - 1))
            {
              trace->push_back_heap(
                step,
                trace->sb_adr(thread),
                trace->sb_val(thread));
            }
          else
            {
              const Instruction & op =
                (*encoder.programs)[thread][trace->pc(thread)];

              if (op.type() & Instruction::Type::atomic && trace->accu(thread))
                {
                  std::string sym = smtlib::Encoder::heap_var(step);

                  word_t address =
                    op.indirect()
                      ? eval_array(c, m, sym, op.arg())
                      : op.arg();

                  trace->push_back_heap(
                    step,
                    address,
                    eval_array(c, m, sym, address));
                }
            }
        }

      // thread states
      for (word_t thread = 0; thread < encoder.programs->size(); thread++)
        {
          if (eval_bool(c, m, smtlib::Encoder::thread_var(step, thread)))
            {
              trace->push_back_thread(step, thread);
            }
          else if (eval_bool(c, m, smtlib::Encoder::flush_var(step, thread)))
            {
              trace->push_back_thread(step, thread);
              trace->push_back_flush(step);
            }

          trace->push_back_accu(
            step,
            thread,
            eval_bv(c, m, smtlib::Encoder::accu_var(step, thread)));
          trace->push_back_mem(
            step,
            thread,
            eval_bv(c, m, smtlib::Encoder::mem_var(step, thread)));
          trace->push_back_sb_adr(
            step,
            thread,
            eval_bv(c, m, smtlib::Encoder::sb_adr_var(step, thread)));
          trace->push_back_sb_val(
            step,
            thread,
            eval_bv(c, m, smtlib::Encoder::sb_val_var(step, thread)));
          trace->push_back_sb_full(
            step,
            thread,
            eval_bool(c, m, smtlib::Encoder::sb_full_var(step, thread)));

          const Program & program = (*encoder.programs)[thread];

          for (word_t pc = 0; pc < program.size(); pc++)
            if (eval_bool(c, m, smtlib::Encoder::stmt_var(step, thread, pc)))
              {
                trace->push_back_pc(step, thread, pc);
                break;
              }
        }

      // exited
      if (eval_bool(c, m, smtlib::Encoder::exit_flag_var(step)))
        break;
    }

  trace->exit = eval_bv(c, m, smtlib::Encoder::exit_code_var);

  return trace;
}

} // namespace ConcuBinE
