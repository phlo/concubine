#include "btormc.hh"

#include "encoder.hh"

namespace ConcuBinE {

BtorMC::BtorMC(size_t b) : bound(b) {}

std::string BtorMC::name () const { return "btormc"; }

std::string BtorMC::build_command ()
{
  return "btormc --trace-gen-full -kmax " + std::to_string(bound);
}

std::string BtorMC::build_formula (Encoder & formula,
                                   const std::string & constraints)
{
  return formula.str() + (constraints.empty() ? "" : constraints + eol);
}

std::optional<BtorMC::Variable> BtorMC::parse_line (std::istringstream & line)
{
  switch (line.peek())
    {
    case 'b':
    case 'j':
    case '#':
    case '@':
    case '.':
      return {};
    default:
      return Boolector::parse_line(line);
    }
}

std::optional<BtorMC::Variable> BtorMC::parse_variable (std::istringstream & line)
{
  std::optional<Variable> variable {Variable()};

  std::ostringstream os;

  // cout << line.str() << eol;

  // if (!getline(line >> ws, name, '_'))
    // runtime_error("missing variable");

  line >> std::ws;

  for (char c = line.get();
       c != '@' && c != '#' && c != '_' && c != EOF;
       c = line.get())
    os << c;

  std::string name = os.str();

  // cout << "BtorMC::parse_variable name = '" << name << '\'' << eol;

  if (name == Encoder::thread_sym)
    {
      variable->type = Variable::Type::THREAD;
      variable->thread = parse_attribute(line, "thread", '@');
      variable->step = parse_attribute(line, "step") + 1;
    }
  else if (name == Encoder::stmt_sym)
    {
      variable->type = Variable::Type::EXEC;
      variable->thread = parse_attribute(line, "thread");
      variable->pc = parse_attribute(line, "pc", '#');
      variable->step = parse_attribute(line, "step") + 1;
    }
  else if (name == Encoder::accu_sym)
    {
      variable->type = Variable::Type::ACCU;
      variable->thread = parse_attribute(line, "thread", '#');
      variable->step = parse_attribute(line, "step");
    }
  else if (name == Encoder::mem_sym)
    {
      variable->type = Variable::Type::MEM;
      variable->thread = parse_attribute(line, "thread", '#');
      variable->step = parse_attribute(line, "step");
    }
  else if (name == Encoder::heap_sym)
    {
      variable->type = Variable::Type::HEAP;
      variable->step = parse_attribute(line, "step", '@');
    }
  else if (name == Encoder::exit_flag_sym)
    {
      variable->type = Variable::Type::EXIT;
      variable->step = parse_attribute(line, "step", '#');
    }
  else if (name == Encoder::exit_code_sym)
    {
      variable->type = Variable::Type::EXIT_CODE;
      variable->step = parse_attribute(line, "step", '#');
    }
  else
    return {};

  /*
  cout << "variable: ";
  switch (variable->type)
    {
    case Variable::Type::THREAD: cout << "THREAD"; break;
    case Variable::Type::EXEC: cout << "EXEC"; break;
    case Variable::Type::ACCU: cout << "ACCU"; break;
    case Variable::Type::MEM: cout << "MEM"; break;
    case Variable::Type::HEAP: cout << "HEAP"; break;
    case Variable::Type::EXIT: cout << "EXIT"; break;
    case Variable::Type::EXIT_CODE: cout << "EXIT_CODE"; break;
    default: ;
    }
  cout << " step = " << variable->step << eol;
  */

  return variable;
}

} // namespace ConcuBinE
