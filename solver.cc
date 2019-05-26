#include "solver.hh"

#include "encoder.hh"
#include "parser.hh"
#include "shell.hh"

using namespace std;

string Solver::build_formula (Encoder & formula, string & constraints)
{
  return formula.str() + eol + (constraints.empty() ? "" : constraints + eol);
}

bool ExternalSolver::sat (string & input)
{
  Shell shell;

  std_out = shell.run(build_command(), input);

  string sat;

  return (std_out >> sat) && sat == "sat";
}

#include <iostream>
SchedulePtr ExternalSolver::solve (Encoder & formula, string & constraints)
{
  string input = build_formula(formula, constraints);

  sat(input);

  return build_schedule(formula.programs);
}

SchedulePtr ExternalSolver::build_schedule (Program_list_ptr programs)
{
  // not really needed
  if (!std_out.rdbuf()->in_avail())
    throw runtime_error(": missing model");

  string sat;

  /* ensure that formula is sat */
  // if (!(std_out >> sat) || sat != "sat")
    // runtime_error("formula is not sat [" + sat + "]");

  SchedulePtr schedule = make_shared<Schedule>(programs);

  /* current line number */
  unsigned long lineno = 2;

  for (string line_buf; getline(std_out >> std::ws, line_buf); lineno++)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      try
        {
          optional<Variable> variable = parse_line(line);

          if (variable)
            {
              switch (variable->type)
                {
                case Variable::Type::THREAD:
                  schedule->push_back_thread(
                    variable->step,
                    variable->thread);
                  break;

                case Variable::Type::EXEC:
                  schedule->push_back_pc(
                    variable->step,
                    variable->thread,
                    variable->pc);
                  break;

                case Variable::Type::ACCU:
                  schedule->push_back_accu(
                    variable->step,
                    variable->thread,
                    variable->val);
                  break;

                case Variable::Type::MEM:
                  schedule->push_back_mem(
                    variable->step,
                    variable->thread,
                    variable->val);
                  break;

                case Variable::Type::HEAP:
                  schedule->push_back_heap(
                    variable->step,
                    {variable->idx, variable->val});
                  break;

                case Variable::Type::EXIT:
                  break;

                case Variable::Type::EXIT_CODE:
                  schedule->exit = variable->val;
                  break;

                default: {}
                }
            }
        }
      catch (const exception & e)
        {
          parser_error(name(), lineno, e.what());
        }
    }

  return schedule;
}

unsigned long Solver::parse_attribute (
                                       istringstream & line,
                                       const string name,
                                       const char delimiter
                                      )
{
  string token;

  if (!getline(line, token, delimiter))
    throw runtime_error("missing " + name);

  try
    {
      return stoul(token);
    }
  catch (...)
    {
      throw runtime_error("illegal " + name + " [" + token + "]");
    }
}

optional<ExternalSolver::Variable>
ExternalSolver::parse_variable (istringstream & line)
{
  optional<Variable> variable {Variable()};

  string name;

  if (!getline(line >> ws, name, '_'))
    throw runtime_error("missing variable");

  if (name == "thread")
    {
      variable->type = Variable::Type::THREAD;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
    }
  else if (name == "exec")
    {
      variable->type = Variable::Type::EXEC;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
      variable->pc = parse_attribute(line, "pc");
    }
  else if (name == "accu")
    {
      variable->type = Variable::Type::ACCU;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
    }
  else if (name == "mem")
    {
      variable->type = Variable::Type::MEM;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
    }
  else if (name == "heap")
    {
      variable->type = Variable::Type::HEAP;
      variable->step = parse_attribute(line, "step");
    }
  else if (name == "exit")
    {
      variable->type = Variable::Type::EXIT;
      variable->step = parse_attribute(line, "step");
    }
  else if (name == "exit-code")
    variable->type = Variable::Type::EXIT_CODE;
  else
    return {};

  return variable;
}
