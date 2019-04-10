#include "boolector.hh"

#include "parser.hh"

using namespace std;

string Boolector::build_command ()
{
  return "boolector --model-gen --output-number-format=dec";
}

SchedulePtr Boolector::build_schedule ()
{
  // not really needed
  if (!std_out.rdbuf()->in_avail())
    throw runtime_error("missing model");

  string token;

  /* ensure that formula is sat */
  if (!(std_out >> token) || token != "sat")
    parser_error("boolector", 1, "formula is not sat [" + token + "]");

  SchedulePtr schedule = make_shared<Schedule>();

  string variable;

  unsigned long nid, step, line_num = 2;

  word tid, pc, accu, mem, idx, val;

  for (string line_buf; getline(std_out, line_buf); line_num++)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* parse node id */
      if (!(line >> nid))
        parser_error("boolector", line_num, "parsing node id failed");

      cout << "nid = " << nid  << " | " << line_buf;

      /* parse value */
      if (!(line >> val))
        {
          line.clear();

          /* array element index */
          if (!(line >> token))
            parser_error("boolector", line_num, "missing array index");

          if (!(istringstream(token.substr(1, token.size() - 2)) >> idx))
              parser_error(
                "boolector",
                line_num,
                "illegal array index [" + token + "]");

          /* array element value */
          if (!(line >> val))
            {
              line.clear();

              if (!(line >> token))
                parser_error("boolector", line_num, "missing array value");

              parser_error(
                "boolector",
                line_num,
                "illegal array value [" + token + "]");
            }

          cout << " | [" << idx << "] = " << val;
        }
      else
        cout << " | " << val;

      /* variable */
      if (!getline(line, variable, '_'))
        parser_error("boolector", line_num, "missing variable");

      if (variable == "exec")
        {
        }
      else if (variable == "accu")
        {
        }
      else if (variable == "mem")
        {
        }
      else if (variable == "heap")
        {
        }

      /* step */
      if (!getline(line, token, '_'))
        parser_error("boolector", line_num, "missing step");

      try
        {
          step = stoul(token);
        }
      catch (...)
        {
          parser_error("boolector", line_num, "illegal step [" + token + "]");
        }

      cout << " | step = " << step;

      (void) step;
      (void) tid;
      (void) pc;
      (void) accu;
      (void) mem;

      cout << eol;
    }

  return schedule;
}
