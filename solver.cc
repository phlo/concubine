#include "solver.hh"

#include <cassert>

#include "encoder.hh"
#include "parser.hh"
#include "shell.hh"
#include "smtlib.hh"

using namespace std;

void Solver::print (Encoder & formula, string & constraints)
{
  cout << build_formula(formula, constraints);
}

bool Solver::sat (string & input)
{
  Shell shell;
  string sat;

  std_out = shell.run(build_command(), input);

  return (std_out >> sat) && sat == "sat";
}

SchedulePtr Solver::solve (Encoder & formula, string & constraints)
{
  Shell shell;

  string input = build_formula(formula, constraints);

  std_out = shell.run(build_command(), input);

  exit_code = shell.last_exit_code();

  // cout << std_out.str();

  return build_schedule(formula.programs);
}

SchedulePtr Solver::build_schedule (ProgramListPtr programs)
{
  // not really needed
  if (!std_out.rdbuf()->in_avail())
    throw runtime_error(": missing model");

  string sat;

  /* ensure that formula is sat */
  if (!(std_out >> sat) || sat != "sat")
    runtime_error("formula is not sat [" + sat + "]");

  SchedulePtr schedule = make_shared<Schedule>(programs);

  /* current line number */
  unsigned long lineno = 2;

  for (string line_buf; getline(std_out, line_buf); lineno++)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      // cout << line_buf << eol;

      try
        {
          optional<Variable> variable = parse_line(line);

          if (variable)
            {
              switch (variable->type)
                {
                case Variable::THREAD:
                  schedule->insert_thread(
                    variable->step,
                    variable->thread);
                  break;

                case Variable::EXEC:
                  schedule->insert_pc(
                    variable->step,
                    variable->thread,
                    variable->pc);
                  break;

                case Variable::ACCU:
                  schedule->insert_accu(
                    variable->step,
                    variable->thread,
                    variable->val);
                  break;

                case Variable::MEM:
                  schedule->insert_mem(
                    variable->step,
                    variable->thread,
                    variable->val);
                  break;

                case Variable::HEAP:
                  schedule->insert_heap(
                    variable->step,
                    {variable->idx, variable->val});
                  break;

                case Variable::EXIT:
                  break;

                case Variable::EXIT_CODE:
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

word Solver::parse_thread (istringstream & line)
{
  string token;

  if (!getline(line, token, '_'))
    throw runtime_error("missing thread id");

  try
    {
      return stoul(token);
    }
  catch (...)
    {
      throw runtime_error("illegal thread id [" + token + "]");
    }
}

word Solver::parse_pc (istringstream & line)
{
  string token;

  if (!getline(line, token, '_'))
    throw runtime_error("missing pc");

  try
    {
      return stoul(token);
    }
  catch (...)
    {
      throw runtime_error("illegal pc [" + token + "]");
    }
}

string SMTLibSolver::build_formula (Encoder & formula, string & constraints)
{
  bound = formula.bound;

  return
    formula.str() + eol +
    (constraints.empty() ? "" : constraints + eol) +
    smtlib::check_sat() + eol;
}

optional<Solver::Variable> SMTLibSolver::parse_variable (istringstream & line)
{
  string name;

  optional<Variable> variable = Variable();

  line >> ws;

  if (!getline(line, name, '_'))
    runtime_error("missing variable");

  if (name == "thread")
    variable->type = Variable::THREAD;
  else if (name == "exec")
    variable->type = Variable::EXEC;
  else if (name == "accu")
    variable->type = Variable::ACCU;
  else if (name == "mem")
    variable->type = Variable::MEM;
  else if (name == "heap")
    variable->type = Variable::HEAP;
  else if (name == "exit")
    variable->type = Variable::EXIT;
  else if (name == "exit-code")
    variable->type = Variable::EXIT_CODE;
  else
    return {};

  switch (variable->type)
    {
    case Variable::THREAD:
      variable->step = parse_step(line);
      variable->thread = parse_thread(line);
      break;

    case Variable::EXEC:
      variable->step = parse_step(line);
      variable->thread = parse_thread(line);
      variable->pc = parse_pc(line);
      break;

    case Variable::ACCU:
      variable->step = parse_step(line);
      variable->thread = parse_thread(line);
      break;

    case Variable::MEM:
      variable->step = parse_step(line);
      variable->thread = parse_thread(line);
      break;

    case Variable::HEAP:
      variable->step = parse_step(line);
      break;

    case Variable::EXIT:
      variable->step = parse_step(line);
      break;

    default: {}
    }

  return variable;
}

unsigned long SMTLibSolver::parse_step (istringstream & line)
{
  string token;

  if (!getline(line, token, '_'))
    throw runtime_error("missing step");

  try
    {
      return stoul(token);
    }
  catch (...)
    {
      throw runtime_error("illegal step [" + token + "]");
    }
}
