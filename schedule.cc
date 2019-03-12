#include "schedule.hh"

#include <sstream>

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Schedule::Schedule () :
  path(""),
  bound(0),
  seed(0),
  exit(0)
{}

Schedule::Schedule (ProgramList & p, unsigned long s, unsigned long b) :
  path(""),
  bound(b),
  seed(s),
  programs(p),
  exit(0)
{}

/* construct from file ********************************************************/
Schedule::Schedule(istream & file, string & name) : path(name), exit(0)
{
  string token;

  bool found_seed = false;

  unsigned long line_num = 1;

  /* parse header */
  for (string line_buf; !found_seed && getline(file, line_buf); line_num++)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* skip comments */
      if (line >> token && token.front() == '#')
        continue;

      /* parse seed */
      if (token == "seed")
        {
          if (line >> token && token != "=")
            parser_error(path, line_num, "'=' expected");

          line >> token;

          try
            {
              seed = stoul(token, nullptr, 0);
              found_seed = true;
            }
          catch (const exception & e)
            {
              parser_error(path, line_num, "illegal seed [" + token + "]");
            }
        }
      /* parse header */
      else
        {
          ThreadID tid;

          try
            {
              tid = stoul(token, nullptr, 0);
            }
          catch (const exception & e)
            {
              parser_error(path, line_num, "illegal thread id [" + token + "]");
            }

          if (programs.empty() && tid)
            parser_error(path, line_num, "thread id must start from zero");

          if (tid != programs.size())
            parser_error(
              path,
              line_num,
              "expected thread id " + to_string(programs.size()));

          if (line >> token && token != "=")
            parser_error(path, line_num, "'=' expected");

          line >> token;

          try
            {
              programs.push_back(ProgramPtr(create_from_file<Program>(token)));
            }
          catch (const exception & e)
            {
              parser_error(
                path,
                line_num,
                e.what());
            }
        }
    }

  /* check header */
  if (programs.empty())
    parser_error(path, line_num, "missing threads");

  /* parse body */
  for (string line_buf; getline(file, line_buf); line_num++)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* skip comments */
      if (line >> token && token.front() == '#')
        continue;

      /* try to parse thread id */
      ThreadID tid;

      try
        {
          tid = stoul(token, nullptr, 0);
        }
      catch (const exception & e)
        {
          parser_error(path, line_num, "illegal thread id [" + token + "]");
        }

      if (tid >= programs.size() || programs[tid] == nullptr)
          parser_error(path, line_num, "unknown thread id [" + token + "]");

      /* append thread id */
      push_back(tid);
    }

  /* set bound */
  bound = size();
}
