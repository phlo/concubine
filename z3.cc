#include "z3.hh"

#include <z3++.h>

#include "encoder.hh"

std::string Z3::name () const { return "z3"; }

bool Z3::sat (const std::string & formula)
{
  z3::context c;
  z3::solver s = c;

  s.from_string(formula.c_str());

  return s.check() == z3::sat;
}

// TODO: replace with SMTLibEncoder variable name generators
inline
std::string symbol (std::string type, std::initializer_list<size_t> attributes)
{
  std::ostringstream os;

  os << type;

  for (const size_t a : attributes)
    os << '_' << a;

  return os.str();
}

inline
bool eval_bool (z3::context & c, const z3::model & m, const std::string sym)
{
  return m.eval(c.bool_const(sym.c_str())).is_true();
}

inline
word_t eval_bv (z3::context & c, const z3::model & m, const std::string sym)
{
  return m.eval(c.bv_const(sym.c_str(), word_size)).get_numeral_uint();
}

inline
word_t eval_array (z3::context & c,
                   const z3::model & m,
                   const std::string sym,
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
  z3::context c;
  z3::solver s = c;

  s.from_string(build_formula(encoder, constraints).c_str());

  if (s.check() != z3::sat)
    throw std::runtime_error("formula is not sat");

  z3::model m = s.get_model();

  Trace::ptr trace = std::make_unique<Trace>(std::move(encoder.programs));

  for (size_t step = 1; step <= encoder.bound; ++step)
    for (word_t thread = 0; thread < encoder.programs->size(); ++thread)
      if (eval_bool(c, m, symbol(Encoder::thread_sym, {step, thread})))
        {
          const Program & program = (*encoder.programs)[thread];

          for (word_t pc = 0; pc < program.size(); ++pc)
            if (eval_bool(c, m, symbol(Encoder::exec_sym, {step, thread, pc})))
              {
                word_t accu =
                  eval_bv(c, m, symbol(Encoder::accu_sym, {step, thread}));
                word_t mem =
                  eval_bv(c, m, symbol(Encoder::mem_sym, {step, thread}));

                std::optional<Trace::cell_t> heap;

                const Instruction & op = program[pc];

                // get eventual heap update (ignore failed CAS)
                // TODO flush!
                if (op.is_memory() && op.type() & Instruction::atomic && accu)
                  {
                    word_t idx = op.arg();

                    if (op.indirect())
                      idx =
                        eval_array(
                          c,
                          m,
                          symbol(Encoder::heap_sym, {step - 1}),
                          idx);

                    heap = {
                      idx,
                      eval_array(c, m, symbol(Encoder::heap_sym, {step}), idx)
                    };
                  }

                // TODO: store buffer
                trace->push_back(thread, pc, accu, mem, 0, 0, false, heap);
              }
        }

  trace->exit = eval_bv(c, m, symbol(Encoder::exit_code_sym, {}));

  return trace;
}
