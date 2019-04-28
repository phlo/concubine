#include "btormc.hh"

#include "encoder.hh"

using namespace std;

BtorMC::BtorMC(unsigned long b) : bound(b) {}

string BtorMC::name () const { return "btormc"; }

string BtorMC::build_command ()
{
  return "btormc --trace-gen-full -kmax " + to_string(bound);
}

string BtorMC::build_formula (Encoder & formula, string & constraints)
{
  return formula.str() + (constraints.empty() ? "" : constraints + eol);
}

optional<BtorMC::Variable> BtorMC::parse_line (istringstream & line)
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

optional<BtorMC::Variable> BtorMC::parse_variable (istringstream & line)
{
  optional<Variable> variable {Variable()};

  ostringstream os;

  // cout << line.str() << eol;

  // if (!getline(line >> ws, name, '_'))
    // runtime_error("missing variable");

  line >> ws;

  for (char c = line.get(); c != '@' && c != '#' && c != '_' && c != EOF; c = line.get())
    os << c;

  string name = os.str();

  // cout << "BtorMC::parse_variable name = '" << name << '\'' << eol;

  if (name == "thread")
    {
      variable->type = Variable::Type::THREAD;
      variable->thread = parse_attribute(line, "thread", '@');
      variable->step = parse_attribute(line, "step") + 1;
    }
  else if (name == "stmt")
    {
      variable->type = Variable::Type::EXEC;
      variable->thread = parse_attribute(line, "thread");
      variable->pc = parse_attribute(line, "pc", '#');
      variable->step = parse_attribute(line, "step") + 1;
    }
  else if (name == "accu")
    {
      variable->type = Variable::Type::ACCU;
      variable->thread = parse_attribute(line, "thread", '#');
      variable->step = parse_attribute(line, "step");
    }
  else if (name == "mem")
    {
      variable->type = Variable::Type::MEM;
      variable->thread = parse_attribute(line, "thread", '#');
      variable->step = parse_attribute(line, "step");
    }
  else if (name == "heap")
    {
      variable->type = Variable::Type::HEAP;
      variable->step = parse_attribute(line, "step", '@');
    }
  else if (name == "exit")
    {
      variable->type = Variable::Type::EXIT;
      variable->step = parse_attribute(line, "step", '#');
    }
  else if (name == "exit-code")
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
