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

BtorMC::Symbol BtorMC::parse_line (std::istringstream & line)
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

BtorMC::Symbol BtorMC::parse_symbol (std::istringstream & line)
{
  std::ostringstream os;

  // cout << line.str() << eol;

  // if (!getline(line >> ws, name, '_'))
    // runtime_error("missing symbol");

  line >> std::ws;

  for (char c = line.get();
       c != '@' && c != '#' && c != '_' && c != EOF;
       c = line.get())
    os << c;

  std::string name = os.str();

  // cout << "BtorMC::parse_variable name = '" << name << '\'' << eol;

  if (name == Encoder::thread_sym)
    {
      thread = parse_symbol(line, "thread", '@');
      step = parse_symbol(line, "step") + 1;
      return Symbol::thread;
    }
  else if (name == Encoder::stmt_sym)
    {
      thread = parse_symbol(line, "thread");
      pc = parse_symbol(line, "pc", '#');
      step = parse_symbol(line, "step") + 1;
      return Symbol::stmt;
    }
  else if (name == Encoder::accu_sym)
    {
      thread = parse_symbol(line, "thread", '#');
      step = parse_symbol(line, "step");
      return Symbol::accu;
    }
  else if (name == Encoder::mem_sym)
    {
      thread = parse_symbol(line, "thread", '#');
      step = parse_symbol(line, "step");
      return Symbol::mem;
    }
  else if (name == Encoder::heap_sym)
    {
      step = parse_symbol(line, "step", '@');
      return Symbol::heap;
    }
  else if (name == Encoder::exit_flag_sym)
    {
      step = parse_symbol(line, "step", '#');
      return Symbol::exit_flag;
    }
  else if (name == Encoder::exit_code_sym)
    {
      step = parse_symbol(line, "step", '#');
      return Symbol::exit_code;
    }

  /*
  cout << "symbol: ";
  switch (symbol->type)
    {
    case Symbol::Type::THREAD: cout << "THREAD"; break;
    case Symbol::Type::EXEC: cout << "EXEC"; break;
    case Symbol::Type::ACCU: cout << "ACCU"; break;
    case Symbol::Type::MEM: cout << "MEM"; break;
    case Symbol::Type::HEAP: cout << "HEAP"; break;
    case Symbol::Type::EXIT: cout << "EXIT"; break;
    case Symbol::Type::EXIT_CODE: cout << "EXIT_CODE"; break;
    default: ;
    }
  cout << " step = " << symbol->step << eol;
  */

  return Symbol::ignore;
}

} // namespace ConcuBinE
