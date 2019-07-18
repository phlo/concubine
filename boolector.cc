#include "boolector.hh"

#include <iomanip>

#include "parser.hh"

namespace ConcuBinE {

std::string Boolector::name () const { return "boolector"; }

std::string Boolector::build_command ()
{
  // return "boolector --model-gen --output-number-format=dec";
  return "boolector --model-gen";
}

std::optional<Boolector::Variable>
Boolector::parse_line (std::istringstream & line)
{
  std::string token;

  uint64_t nid;

  word_t adr = 0, val = 0;

  // parse node id
  if (!(line >> nid))
    {
      line >> token;
      throw std::runtime_error("parsing node id failed [" + token + ']');
    }

  // parse value
  if (!(line >> token))
    throw std::runtime_error("missing value");

  try
    {
      val = stoul(token, nullptr, 2);
    }
  catch (const std::logic_error &)
    {
      // array element index
      try
        {
          token = token.substr(1, token.size() - 2);
          adr = stoul(token, nullptr, 2);
        }
      catch (const std::logic_error &)
        {
          throw std::runtime_error("illegal array index [" + token + "]");
        }

      // array element value
      if (!(line >> token))
        throw std::runtime_error("missing array value");

      try
        {
          val = stoul(token, nullptr, 2);
        }
      catch (const std::logic_error &)
        {
          throw std::runtime_error("illegal array value [" + token + "]");
        }
    }

  // parse variable
  std::optional<Variable> variable = parse_variable(line);

  /*
  if (variable && variable->type == Variable::Type::EXEC && val)
    {
      cout
        << "exec step = " << variable->step
        << " thread = " << variable->thread
        << " pc = " << variable->pc << eol;
    }

  if (variable && variable->step)
    {
      cout << "\tvariable: ";
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
    }
  */

  if (variable && variable->step)
    switch (variable->type)
      {
      case Variable::Type::THREAD:
      case Variable::Type::EXEC:
      case Variable::Type::EXIT:
        if (val)
          return variable;
        break;

      case Variable::Type::ACCU:
      case Variable::Type::MEM:
      case Variable::Type::EXIT_CODE:
        variable->val = val;
        return variable;

      case Variable::Type::HEAP:
        variable->adr = adr;
        variable->val = val;
        return variable;

      default: {}
      }

  return {};
}

} // namespace ConcuBinE
