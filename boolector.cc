#include "boolector.hh"

#include "parser.hh"

using namespace std;

string Boolector::name () const { return "boolector"; }

string Boolector::build_command ()
{
  return "boolector --model-gen --output-number-format=dec";
}

optional<Boolector::Variable> Boolector::parse_line (istringstream & line)
{
  string token;

  unsigned long nid;

  word idx = 0, val = 0;

  /* parse node id */
  if (!(line >> nid))
    throw runtime_error("parsing node id failed");

  /* parse value */
  if (!(line >> val))
    {
      line.clear();

      /* array element index */
      if (!(line >> token))
        runtime_error("missing array index");

      try
        {
          token = token.substr(1, token.size() - 2);
          idx = stoul(token);
        }
      catch (...)
        {
          runtime_error("illegal array index [" + token + "]");
        }

      /* array element value */
      if (!(line >> val))
        {
          line.clear();

          if (!(line >> token))
            runtime_error("missing array value");

          runtime_error("illegal array value [" + token + "]");
        }
    }

  /* parse variable */
  optional<Variable> variable = parse_variable(line);

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
        variable->idx = idx;
        variable->val = val;
        return variable;

      default: {}
      }

  return {};
}
