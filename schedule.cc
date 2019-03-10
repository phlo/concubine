#include "schedule.hh"

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Schedule::Schedule () :
  path(""),
  bound(0),
  seed(0),
  programs(new ProgramList()),
  exit(0)
{}

Schedule::Schedule (ProgramList & p, unsigned long s, unsigned long b) :
  path(""),
  bound(b),
  seed(s),
  programs(make_shared<ProgramList>(p)),
  exit(0)
{}

/* construct from file ********************************************************/
Schedule::Schedule(istream & file, string & name) :
  path(name),
  programs(new ProgramList())
{
  string token;

  bool found_seed = false;

  /* parse header */
  while (file && !found_seed)
    {
      if (file.peek() == '#')
        {
          getline(file, token);
          continue;
        }

      file >> token;

      /* parse seed */
      if (token == "seed")
        {
          if (file >> token && token != "=")
            throw runtime_error("'=' expected");

          file >> token;

          try
            {
              seed = stoul(token, nullptr, 0);
              found_seed = true;
            }
          catch (const exception & e)
            {
              throw runtime_error("illegal seed [" + token + "]");
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
              throw runtime_error("illegal thread id [" + token + "]");
            }

          if (file >> token && token != "=")
            throw runtime_error("'=' expected");

          file >> token;

          programs->at(tid - 1) = ProgramPtr(create_from_file<Program>(token));
        }
    }

  /* check header */
  if (programs->empty())
    throw runtime_error("missing threads");

  /* parse body */
  while (file && file >> token)
    {
      if (token[0] == '#')
        {
          getline(file, token);
          continue;
        }

      /* try to parse thread id */
      ThreadID tid;

      try
        {
          tid = stoul(token, nullptr, 0);
        }
      catch (const exception & e)
        {
          throw runtime_error("illegal thread id [" + token + "]");
        }

      if (tid >= programs->size() || programs->at(tid) == nullptr)
          throw runtime_error("unknown thread id");

      add(tid);

      /* ignore rest of the line (in case of verbose output) */
      getline(file, token);
    }

  /* set bound */
  bound = size();
}

/* Schedule::add (ThreadID, ProgramPtr) ***************************************/
void Schedule::add (ThreadID tid, ProgramPtr program)
{
  programs->at(tid) = program;
}

/* Schedule::add (ThreadID) ***************************************************/
void Schedule::add (ThreadID tid) { push_back(tid); }
