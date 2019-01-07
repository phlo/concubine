#include <deque>
#include <string>
#include <cstring>
#include <iostream>
#include <stdexcept>

#include "parser.hh"
#include "encoder.hh"
#include "machine.hh"
#include "verifier.hh"
#include "boolector.hh"

using namespace std;

/* global flags ***************************************************************/
bool verbose = false;

/* usage output ***************************************************************/
void print_usage_main (char * name)
{
  cout << "usage: " << name <<
  " <command> [<arg> ...]" <<
  endl << endl <<
  "available commands:" << endl <<
  "  help       print help for a specific <command>" << endl <<
  "  simulate   simulate concurrent programs" << endl <<
  "  replay     reevaluates a given schedule" << endl <<
  "  verify     verifies a given (single-threaded) program" << endl;
}

void print_usage_help (char * name)
{
  cout << "usage: " << name << " help <command>" << endl;
}

void print_usage_simulate (char * name)
{
  cout << "usage: " << name <<
  " simulate [-v] [-s <seed>] [-k <bound>] <program> ..." <<
  endl << endl <<
  "  -v         verbose schedule output" << endl <<
  "  -s seed    random number generator's seed" << endl <<
  "  -k bound   execute a maximum of <bound> steps" << endl <<
  "  program    one ore more source files, each being executed as a separate thread" << endl;
}

void print_usage_replay (char * name)
{
  cout << "usage: " << name <<
  " replay [-v] [-k <bound>] <schedule>" <<
  endl << endl <<
  "  -v         verbose schedule output" << endl <<
  "  -k bound   execute a maximum of <bound> steps" << endl <<
  "  schedule   the schedule to replay" << endl;
}

void print_usage_verify (char * name)
{
  cout << "usage: " << name <<
  " verify [-p] <bound> <program> <specification>" <<
  endl << endl <<
  "  -p         prints the generated SMT-Lib v2 file and exits" << endl <<
  "  bound      execute a maximum of <bound> steps" << endl <<
  "  program    the program to encode" << endl;
}

/*******************************************************************************
 * main functions
 ******************************************************************************/
void print_error (string what) { cerr << "error: " << what << endl; }

/* help ***********************************************************************/
int help (char * name, int argc, char **argv)
{
  if (argc < 1)
    {
      print_error("no command given");
      print_usage_help(name);
      return -1;
    }

  if (!strcmp(argv[0], "help"))
    {
      print_usage_help(name);
    }
  else if (!strcmp(argv[0], "simulate"))
    {
      print_usage_simulate(name);
    }
  else if (!strcmp(argv[0], "replay"))
    {
      print_usage_replay(name);
    }
  else if (!strcmp(argv[0], "verify"))
    {
      print_usage_verify(name);
    }
  else
    {
      print_error("unknown command " + string(argv[0]));
      print_usage_help(name);
      return -1;
    }

  return 0;
}

/* simulate *******************************************************************/
int simulate (char * name, int argc, char ** argv)
{
  unsigned int      seed = time(NULL);
  unsigned int      bound = 0;
  ProgramList       threads;

  for (int i = 0; i < argc; i++)
    {
      string arg(argv[i]);

      if (arg == "-v")
        {
          verbose = true;
        }
      else if (arg == "-s")
        {
          try
            {
              if (++i < argc)
                seed = stoul((arg = argv[i]), nullptr, 0);
              else
                {
                  print_error("missing seed");
                  return -1;
                }
            }
          catch (...)
            {
              print_error("illegal seed [" + arg + "]");
              return -1;
            }
        }
      else if (arg == "-k")
        {
          try
            {
              if (++i < argc)
                bound = stoul((arg = argv[i]), nullptr, 0);
              else
                {
                  print_error("missing bound");
                  return -1;
                }
            }
          catch (...)
            {
              print_error("illegal bound [" + arg + "]");
              return -1;
            }
        }
      else
        {
          try
            {
              threads.push_back(make_shared<Program>(arg));
            }
          catch (const exception & e)
            {
              print_error(e.what());
              return -1;
            }
        }
    }

  if (threads.empty())
    {
      print_error("got nothing to run");
      print_usage_simulate(name);
      return -1;
    }

  /* run program with given seed */
  Machine machine(seed, bound);
  for (auto p : threads)
    machine.create_thread(*p);

  return machine.simulate();
}

/* replay *********************************************************************/
int replay (char * name, int argc, char ** argv)
{
  if (argc < 1)
    {
      print_error("no schedule given");
      print_usage_replay(name);
      return -1;
    }

  unsigned int      bound = 0;
  string            path2schedule;

  for (int i = 0; i < argc; i++)
    {
      string arg(argv[i]);

      if (arg == "-v")
        {
          verbose = true;
        }
      else if (arg == "-k")
        {
          try
            {
              if (++i < argc)
                bound = stoul((arg = argv[i]), nullptr, 0);
              else
                {
                  print_error("missing bound");
                  return -1;
                }
            }
          catch (...)
            {
              print_error("illegal bound [" + arg + "]");
              return -1;
            }
        }
      else
        {
          path2schedule = arg;
        }
    }

  try
    {
      /* create and parse schedule */
      Schedule schedule(path2schedule);

      /* run given schedule */
      Machine machine(schedule.seed, bound);

      return machine.replay(schedule);
    }
  catch (const exception & e)
    {
      print_error(e.what());
      return -1;
    }
}

/* verify *********************************************************************/
int verify (char * name, int argc, char ** argv)
{
  if (argc < 2)
    {
      print_error("too few arguments");
      print_usage_verify(name);
      return -1;
    }

  int i = 0;

  /* only print smt file if true */
  bool pretend = false;

  /* check pretend flag */
  if (!strcmp(argv[i], "-p"))
    {
      pretend = true;
      i++;
    }

  /* check for bound and program */
  if (argc < i + 1)
    {
      print_error("too few arguments");
      print_usage_verify(name);
      return -1;
    }

  /* parse bound */
  unsigned long bound = 0;
  try
    {
      bound = stoul(argv[i++], nullptr, 0);

      if (bound < 1) throw runtime_error("");
    }
  catch (...)
    {
      print_error("illegal bound [" + string(argv[i-1]) + "]");
      return -1;
    }

  try
    {
      /* list of programs (idx == thread id) */
      ProgramListPtr programs(new ProgramList());

      /* parse programs */
      while (i < argc)
        programs->push_back(ProgramPtr(new Program(argv[i++])));

      /* encode program */
      SMTLibEncoderFunctional formula(programs, bound);

      // TODO: encode implicitly?
      formula.encode();

      /* read specification from file */
      string specification;

      /* create solver */
      Boolector boolector;

      /* create verifier*/
      Verifier verifier(boolector, formula, specification);

      /* print program if we're pretending */
      if (pretend)
        verifier.print();
      else
        return verifier.sat();
    }
  catch (const exception & e)
    {
      print_error(e.what());
      return -1;
    }

  return 0;
}

/* main ***********************************************************************/
int main (int argc, char ** argv)
{
  if (argc > 1)
    {
      /* forward to given command's main */
      if (!strcmp(argv[1], "help"))
        {
          return help(argv[0], argc - 2, argv + 2);
        }
      else if (!strcmp(argv[1], "simulate"))
        {
          return simulate(argv[0], argc - 2, argv + 2);
        }
      else if (!strcmp(argv[1], "replay"))
        {
          return replay(argv[0], argc - 2, argv + 2);
        }
      else if (!strcmp(argv[1], "verify"))
        {
          return verify(argv[0], argc - 2, argv + 2);
        }
    }

  /* found no command */
  print_usage_main(argv[0]);
  return -1;
}
