#include "z3.hh"

#include <z3++.h>

#include "encoder.hh"

using namespace std;

string Z3::name () const { return "z3"; }

bool Z3::sat (std::string & formula)
{
  z3::context c;
  z3::solver s = c;

  s.from_string(formula.c_str());

  return s.check() == z3::sat;
}

// TODO: replace with SMTLibEncoder variable name generators
inline
string symbol (string type, initializer_list<unsigned long> attributes)
{
  ostringstream os;

  os << type;

  for (const unsigned long a : attributes)
    os << '_' << a;

  return os.str();
}

inline
bool eval_bool (z3::context & c, const z3::model & m, const string sym)
{
  return m.eval(c.bool_const(sym.c_str())).is_true();
}

inline
word eval_bv (z3::context & c, const z3::model & m, const string sym)
{
  return m.eval(c.bv_const(sym.c_str(), word_size)).get_numeral_uint();
}

inline
word eval_array (z3::context & c, const z3::model & m, const string sym, const word idx)
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

SchedulePtr Z3::solve (Encoder & encoder, string & constraints)
{
  z3::context c;
  z3::solver s = c;

  s.from_string(build_formula(encoder, constraints).c_str());

  if (s.check() != z3::sat)
    throw runtime_error("formula is not sat");

  z3::model m = s.get_model();

  SchedulePtr schedule = make_shared<Schedule>(encoder.programs);

  for (unsigned long step = 1; step <= encoder.bound; ++step)
    for (unsigned long thread = 0; thread < encoder.programs->size(); ++thread)
      if (eval_bool(c, m, symbol("thread", {step, thread})))
        {
          Program & program = *(*encoder.programs)[thread];

          for (word pc = 0; pc < program.size(); ++pc)
            if (eval_bool(c, m, symbol("exec", {step, thread, pc})))
              {
                word accu = eval_bv(c, m, symbol("accu", {step, thread}));
                word mem = eval_bv(c, m, symbol("mem", {step, thread}));

                optional<Schedule::Heap_Cell> heap;

                /* get eventual heap update (ignore failed CAS) */
                if (Store_ptr store = dynamic_pointer_cast<Store>(program[pc]))
                  if (!(store->type() & Instruction::Types::atomic) || accu)
                    {
                      word idx = store->arg;

                      if (store->indirect)
                        idx = eval_array(c, m, symbol("heap", {step - 1}), idx);

                      heap = {idx, eval_array(c, m, symbol("heap", {step}), idx)};
                    }

                schedule->push_back(thread, pc, accu, mem, heap);
              }
        }

  schedule->exit = eval_bv(c, m, symbol("exit-code", {}));

  return schedule;
}
