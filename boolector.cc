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

#ifdef DEPRECATED
SchedulePtr build_schedule ()
{
  stringstream std_out;

  // not really needed
  if (!std_out.rdbuf()->in_avail())
    throw runtime_error("missing model");

  string token;

  /* ensure that formula is sat */
  if (!(std_out >> token) || token != "sat")
    parser_error("boolector", 1, "formula is not sat [" + token + "]");

  SchedulePtr schedule = make_shared<Schedule>();

  string variable;

  Schedule::step_t step;

  unsigned long nid;

  /* current and previous line's step numbers */
  unsigned long step_cur = 0, step_prev = step_cur;

  /* current line number */
  unsigned long lineno = 2;

  word tid, pc, accu, mem, idx, val;

  for (string line_buf; getline(std_out, line_buf); lineno++)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* parse node id */
      if (!(line >> nid))
        parser_error("boolector", lineno, "parsing node id failed");

      cout << "nid = " << nid  << " | " << line_buf;

      /* parse value */
      if (!(line >> val))
        {
          line.clear();

          /* array element index */
          if (!(line >> token))
            parser_error("boolector", lineno, "missing array index");

          try
            {
              token = token.substr(1, token.size() - 2);
              idx = stoul(token);
            }
          catch (...)
            {
              parser_error(
                "boolector",
                lineno,
                "illegal array index [" + token + "]");
            }

          /* array element value */
          if (!(line >> val))
            {
              line.clear();

              if (!(line >> token))
                parser_error("boolector", lineno, "missing array value");

              parser_error(
                "boolector",
                lineno,
                "illegal array value [" + token + "]");
            }

          cout << " | [" << idx << "] = " << val;
        }
      else
        cout << " | " << val;

      /* variable */
      if (!getline(line, variable, '_'))
        parser_error("boolector", lineno, "missing variable");

      /* step */
      parse_step(step_cur, line, lineno, token);

      cout << " | step = " << step_cur;

      /* finished current step - append to schedule */
      if (step_cur != step_prev)
        {
          cout << " | " << " next";
          step_prev = step_cur;
          step = {};
        }

      /* parse context */
      if (variable == "thread" && val)
        {
          parse_tid(tid, line, lineno, token);
        }
      else if (variable == "exec" && val)
        {
          // parse_tid(tid, line, lineno, token);
          parse_pc(pc, line, lineno, token);
        }
      else if (variable == "accu")
        {
          /* assumption: current tid has already been parsed */
        }
      else if (variable == "mem")
        {
        }
      else if (variable == "heap")
        {
        }

      (void) step;
      (void) step_prev;
      (void) tid;
      (void) pc;
      (void) accu;
      (void) mem;

      cout << eol;
    }

  return schedule;
}
#endif
