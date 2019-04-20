#include "z3.hh"

#include <z3++.h>

#include "encoder.hh"

using namespace std;

string Z3::name () { return "z3"; }

// TODO: deprecate
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

bool Z3::sat (std::string & formula)
{
  z3::context context;

  z3::solver solver {context};

  solver.from_string(formula.c_str());

  z3::check_result result {solver.check()};

  std_out << result << eol;

  return result == z3::sat;
}

SchedulePtr Z3::solve (Encoder & encoder, string & constraints)
{
  string formula {build_formula(encoder, constraints)};

  z3::context context;

  z3::solver solver {context};

  z3::set_param("model_compress", "false");
  // z3::set_param("pp.single_line", "true");

  solver.from_string(formula.c_str());

  std_out << solver.check() << eol;

  z3::model model {solver.get_model()};

  z3::expr_vector variables {context};

  for (unsigned long step = 1; step <= encoder.bound; ++step)
    {
      ostringstream name;

      if (step > 1)
        {
          name << "exit_" << step;
          variables.push_back(context.bool_const(name.str().c_str()));
        }

      for (unsigned long thread = 0; thread < encoder.num_threads; ++thread)
        {
          name.str("");
          name << "thread_" << step << '_' << thread;
          variables.push_back(context.bool_const(name.str().c_str()));

          unsigned long program_size = encoder.programs->at(thread)->size();

          for (unsigned long pc = 0; pc < program_size; ++pc)
            {
              name.str("");
              name << "exec_" << step << '_' << thread << '_' << pc;
              variables.push_back(context.bool_const(name.str().c_str()));
            }

          name.str("");
          name << "accu_" << step << '_' << thread;
          variables.push_back(context.bv_const(name.str().c_str(), word_size));

          name.str("");
          name << "mem_" << step << '_' << thread;
          variables.push_back(context.bv_const(name.str().c_str(), word_size));
        }

      name.str("");
      name << "heap_" << step;
      variables.push_back(
        context.constant(
          name.str().c_str(),
          context.array_sort(
            context.bv_sort(word_size),
            context.bv_sort(word_size))));
    }

  variables.push_back(context.bv_const("exit-code", word_size));

  for (const z3::expr & var : variables)
    std_out << var.decl().name().str() << " = " << model.eval(var) << eol;

  cout << std_out.str();

  return build_schedule(encoder.programs);
}

optional<Solver::Variable> Z3::parse_line (istringstream & line)
{
  (void) line;

  return {};
}
