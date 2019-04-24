#include "z3.hh"

#include <z3++.h>

#include "encoder.hh"

using namespace std;

Z3::Z3 () : solver {context} {}

string Z3::name () { return "z3"; }

// TODO: remove
/*
string Z3::build_command ()
{
  return "z3 "
    "dump_models=true "
    "model_compress=false "
    "model.v2=true "
    "pp.single_line=true "
    "-in";

  // NOTES:
  // * smtlib2_compliant=true -> unsat!?
}
*/

bool Z3::sat (std::string & formula)
{
  solver.from_string(formula.c_str());

  z3::check_result result {solver.check()};

  return result == z3::sat;
}

inline
bool get_exec (
               z3::context & context,
               const z3::model & model,
               const unsigned long step,
               const word thread,
               const word pc
              )
{
  ostringstream name;

  name << "exec_" << step << '_' << thread << '_' << pc;

  return model.eval(context.bool_const(name.str().c_str())).is_true();
}

inline
word get_accu (
               z3::context & context,
               const z3::model & model,
               const unsigned long step,
               const word thread
              )
{
  ostringstream name;

  name << "accu_" << step << '_' << thread;

  return static_cast<word>(
    model.eval(
      context.bv_const(name.str().c_str(), word_size))
    .get_numeral_uint());
}

inline
word get_mem (
              z3::context & context,
              const z3::model & model,
              const unsigned long step,
              const word thread
             )
{
  ostringstream name;

  name << "mem_" << step << '_' << thread;

  return static_cast<word>(
    model.eval(
      context.bv_const(name.str().c_str(), word_size))
    .get_numeral_uint());
}

inline
z3::expr get_heap_var (z3::context & context, const unsigned long step)
{
  ostringstream name;

  name << "heap_" << step;

  return
    context.constant(
      name.str().c_str(),
      context.array_sort(
        context.bv_sort(word_size),
        context.bv_sort(word_size)));
}

inline
std::optional<Schedule::Heap_Cell>
get_heap_update (
                 z3::context & context,
                 const z3::model & model,
                 const unsigned long step,
                 const InstructionPtr cmd,
                 const word accu
                )
{
  optional<Schedule::Heap_Cell> heap;

  if (StorePtr store = dynamic_pointer_cast<Store>(cmd))
    {
      /* ignore failed CAS */
      if (store->get_opcode() == Instruction::OPCode::Store || accu)
        {
          z3::expr idx {context.bv_val(store->arg, word_size)};

          if (store->indirect)
            idx = model.eval(z3::select(get_heap_var(context, step - 1), idx));

          heap = {
            static_cast<word>(idx.get_numeral_uint()),
            static_cast<word>(
              model.eval(
                z3::select(get_heap_var(context, step), idx))
              .get_numeral_uint())};
        }
    }

  return heap;
}

SchedulePtr Z3::solve (Encoder & encoder, string & constraints)
{
  string formula {build_formula(encoder, constraints)};

  z3::set_param("model_compress", "false");
  // z3::set_param("pp.single_line", "true");

  solver.from_string(formula.c_str());

  // std_out << solver.check() << eol;

  SchedulePtr schedule = make_shared<Schedule>(encoder.programs);

  z3::model model {solver.get_model()};

  size_t num_threads {encoder.programs->size()};

  for (unsigned long step = 1; step <= encoder.bound; ++step)
    {
      for (unsigned long thread = 0; thread < num_threads; ++thread)
        {
          Program & program {*encoder.programs->at(thread)};

          /* find executed instruction */
          for (word pc {0}; pc < program.size(); ++pc)
            {
              if (get_exec(context, model, step, thread, pc))
                {
                  word accu {get_accu(context, model, step, thread)};

                  word mem {get_mem(context, model, step, thread)};

                  /* eventual heap update */
                  optional<Schedule::Heap_Cell> heap;

                  if (StorePtr store = dynamic_pointer_cast<Store>(program.at(pc)))
                    {
                      /* ignore failed CAS */
                      if (store->get_opcode() == Instruction::OPCode::Store || accu)
                        {
                          z3::expr idx {context.bv_val(store->arg, word_size)};

                          if (store->indirect)
                            idx = model.eval(z3::select(get_heap_var(context, step - 1), idx));

                          heap = {
                            static_cast<word>(idx.get_numeral_uint()),
                            static_cast<word>(
                              model.eval(
                                z3::select(get_heap_var(context, step), idx))
                              .get_numeral_uint())};
                        }
                    }

                  schedule->push_back(thread, pc, accu, mem, heap);
                }
            }
        }
    }

  schedule->exit =
    static_cast<word>(
      model.eval(
        context.bv_const("exit-code", word_size))
      .get_numeral_uint());

  cout << schedule->print();

  return schedule;
}

z3::expr Z3::heap_var (unsigned long step)
{
  ostringstream name;
  name << "heap_" << step;

  return
    context.constant(
      name.str().c_str(),
      context.array_sort(
        context.bv_sort(word_size),
        context.bv_sort(word_size)));
}

SchedulePtr Z3::build_schedule (ProgramListPtr programs, unsigned long bound)
{
  SchedulePtr schedule = make_shared<Schedule>(programs);

  z3::model model {solver.get_model()};

  size_t num_threads {programs->size()};

  for (unsigned long step = 1; step <= bound; ++step)
    {

      for (unsigned long thread = 0; thread < num_threads; ++thread)
        {
          Program & program {*programs->at(thread)};

          /* find executed instruction */
          for (word pc {0}; pc < program.size(); ++pc)
            {
              ostringstream name;

              name << "exec_" << step << '_' << thread << '_' << pc;

              z3::expr var {context.bool_const(name.str().c_str())};
              z3::expr val {model.eval(var)};

              if (val.is_true())
                {
                  cout << var.decl().name().str() << " = " << val << eol;

                  /* get accu */
                  name.str("");
                  name << "accu_" << step << '_' << thread;

                  var = context.bv_const(name.str().c_str(), word_size);
                  val = model.eval(var);

                  cout << var.decl().name().str() << " = " << val << eol;

                  word accu {static_cast<word>(val.get_numeral_uint())};

                  /* get mem */
                  name.str("");
                  name << "mem_" << step << '_' << thread;

                  var = context.bv_const(name.str().c_str(), word_size);
                  val = model.eval(var);

                  cout << var.decl().name().str() << " = " << val << eol;

                  word mem {static_cast<word>(val.get_numeral_uint())};

                  optional<Schedule::Heap_Cell> heap;

                  /* get eventual heap update (ignore failed CAS) */
                  if (StorePtr store = dynamic_pointer_cast<Store>(program.at(pc)))
                    {
                      if (store->get_opcode() == Instruction::OPCode::Store || accu)
                        {
                          z3::expr idx {context.bv_val(store->arg, word_size)};

                          if (store->indirect)
                            {
                              var = heap_var(step - 1);
                              idx = model.eval(z3::select(var, idx));
                            }

                          var = heap_var(step);
                          val = model.eval(z3::select(var, idx));

                          cout << var.decl().name().str() << " += {" << idx << ", " << val << '}' << eol;

                          heap = {
                            static_cast<word>(idx.get_numeral_uint()),
                            static_cast<word>(val.get_numeral_uint())};
                        }
                    }

                  schedule->push_back(thread, pc, accu, mem, heap);
                }
            }
        }
    }

  schedule->exit =
    static_cast<word>(
      model.eval(
        context.bv_const("exit-code", word_size))
      .get_numeral_uint());

  cout << schedule->print();

  return schedule;
}
