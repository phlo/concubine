#include "solver.hh"

#include "encoder.hh"
#include "parser.hh"
#include "shell.hh"

//==============================================================================
// Solver
//==============================================================================

// Solver::parse_attribute -----------------------------------------------------

bound_t Solver::parse_attribute (std::istringstream & line,
                                 const std::string & name,
                                 const char delimiter)
{
  std::string token;

  if (!getline(line, token, delimiter))
    throw std::runtime_error("missing " + name);

  try
    {
      return stoul(token);
    }
  catch (...)
    {
      throw std::runtime_error("illegal " + name + " [" + token + "]");
    }
}

// Solver::build_formula -------------------------------------------------------

std::string Solver::build_formula (Encoder & formula,
                                   const std::string & constraints)
{
  return formula.str() + eol + (constraints.empty() ? "" : constraints + eol);
}

//==============================================================================
// External
//==============================================================================

// External::sat ---------------------------------------------------------------

bool External::sat (const std::string & input)
{
  Shell shell;

  std_out = shell.run(build_command(), input);

  std::string sat;

  return (std_out >> sat) && sat == "sat";
}

// External::solve -------------------------------------------------------------

Trace::ptr External::solve (Encoder & formula, const std::string & constraints)
{
  std::string input = build_formula(formula, constraints);

  sat(input);

  std::unique_ptr<Trace> s = build_trace(formula.programs);

  return s;

  // return build_trace(formula.programs);
}

// External::build_trace -------------------------------------------------------

Trace::ptr External::build_trace (const Program::List::ptr & programs)
{
  // not really needed
  if (!std_out.rdbuf()->in_avail())
    throw std::runtime_error(": missing model");

  std::string sat;

  // ensure that formula is sat
  // if (!(std_out >> sat) || sat != "sat")
    // runtime_error("formula is not sat [" + sat + "]");

  Trace::ptr trace = std::make_unique<Trace>(programs);

  // current line number
  size_t lineno = 2;

  for (std::string line_buf; getline(std_out >> std::ws, line_buf); lineno++)
    {
      // skip empty lines
      if (line_buf.empty())
        continue;

      std::istringstream line(line_buf);

      try
        {
          std::optional<Variable> variable = parse_line(line);

          if (variable)
            {
              switch (variable->type)
                {
                case Variable::Type::THREAD:
                  trace->insert_thread(
                    variable->step,
                    variable->thread);
                  break;

                case Variable::Type::EXEC:
                  trace->insert_pc(
                    variable->step,
                    variable->thread,
                    variable->pc);
                  break;

                case Variable::Type::ACCU:
                  trace->insert_accu(
                    variable->step,
                    variable->thread,
                    variable->val);
                  break;

                case Variable::Type::MEM:
                  trace->insert_mem(
                    variable->step,
                    variable->thread,
                    variable->val);
                  break;

                case Variable::Type::HEAP:
                  trace->insert_heap(
                    variable->step,
                    {variable->adr, variable->val});
                  break;

                case Variable::Type::EXIT:
                  break;

                case Variable::Type::EXIT_CODE:
                  trace->exit = variable->val;
                  break;

                default: {}
                }
            }
        }
      catch (const std::exception & e)
        {
          parser_error(name(), lineno, e.what());
        }
    }

  return trace;
}

// External::parse_variable ----------------------------------------------------

std::optional<External::Variable>
External::parse_variable (std::istringstream & line)
{
  std::optional<Variable> variable {Variable()};

  std::string name;

  if (!getline(line >> std::ws, name, '_'))
    throw std::runtime_error("missing variable");

  if (name == Encoder::thread_sym)
    {
      variable->type = Variable::Type::THREAD;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
    }
  else if (name == Encoder::exec_sym)
    {
      variable->type = Variable::Type::EXEC;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
      variable->pc = parse_attribute(line, "pc");
    }
  else if (name == Encoder::accu_sym)
    {
      variable->type = Variable::Type::ACCU;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
    }
  else if (name == Encoder::mem_sym)
    {
      variable->type = Variable::Type::MEM;
      variable->step = parse_attribute(line, "step");
      variable->thread = parse_attribute(line, "thread");
    }
  else if (name == Encoder::heap_sym)
    {
      variable->type = Variable::Type::HEAP;
      variable->step = parse_attribute(line, "step");
    }
  else if (name == Encoder::exit_flag_sym)
    {
      variable->type = Variable::Type::EXIT;
      variable->step = parse_attribute(line, "step");
    }
  else if (name == Encoder::exit_code_sym)
    variable->type = Variable::Type::EXIT_CODE;
  else
    return {};

  return variable;
}
