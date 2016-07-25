#include <deque>
#include <string>
#include <cstring>
#include <iostream>
#include <stdexcept>

#include "parser.hh"
#include "machine.hh"

using namespace std;

/* global flags ***************************************************************/
bool verbose = false;

/* usage output ***************************************************************/
void printUsageMain (char * name)
{
  cout << "usage: " << name <<
  " <command> [<arg> ...]" <<
  endl << endl <<
  "available commands:" << endl <<
  "  help       print help for a specific <command>" << endl <<
  "  simulate   simulate concurrent programs" << endl <<
  "  replay     reevaluates a given schedule" << endl;
}

void printUsageHelp (char * name)
{
  cout << "usage: " << name << " help <command>" << endl;
}

void printUsageSimulate (char * name)
{
  cout << "usage: " << name <<
  " simulate [-v] [-s <seed>] [-k <bound>] <program> ..." <<
  endl << endl <<
  "  -v         verbose schedule output" << endl <<
  "  -s seed    random number generator's seed" << endl <<
  "  -k bound   execute a maximum of <bound> steps" << endl <<
  "  program    one ore more source files, each being executed as a separate thread" << endl;
}

void printUsageReplay (char * name)
{
  cout << "usage: " << name <<
  " replay [-v] [-k <bound>] <schedule>" <<
  endl << endl <<
  "  -v         verbose schedule output" << endl <<
  "  -k bound   execute a maximum of <bound> steps" << endl <<
  "  schedule   the schedule to replay" << endl;
}

/*******************************************************************************
 * main functions
 * TODO: error handling!!!
 ******************************************************************************/

/* help ***********************************************************************/
int help (char * name, int argc, char **argv)
{
  if (argc < 1)
    {
      cout << "no command given" << endl << endl;
      printUsageHelp(name);
      return -1;
    }

  if (!strcmp(argv[0], "help"))
    {
      printUsageHelp(name);
    }
  else if (!strcmp(argv[0], "simulate"))
    {
      printUsageSimulate(name);
    }
  else if (!strcmp(argv[0], "replay"))
    {
      printUsageReplay(name);
    }
  else
    {
      cout << "unknown command '" << argv[0] << "'" << endl << endl;
      printUsageHelp(name);
      return -1;
    }

  return 0;
}

/* simulate *******************************************************************/
int simulate (char * name, int argc, char ** argv)
{
  unsigned int      seed = time(NULL);
  unsigned int      bound = 0;
  deque<Program *>  threads;

  for (int i = 0; i < argc; i++)
    {
      string arg(argv[i]);

      if (arg == "-v")
        {
          verbose = true;
        }
      else if (arg == "-s")
        {
          // throws std::invalid_argument
          seed = stoul((arg = argv[++i]), nullptr, 0);
        }
      else if (arg == "-k")
        {
          // throws std::invalid_argument
          bound = stoul((arg = argv[++i]), nullptr, 0);
        }
      else
        {
          threads.push_back(new Program(arg));
        }
    }

  if (threads.empty())
    {
      cout << "got nothing to run" << endl;
      printUsageSimulate(name);
      return -1;
    }

  /* run program with given seed */
  Machine machine(seed, bound);
  for (auto p : threads)
    machine.createThread(*p);

  return machine.simulate();
}

/* replay *********************************************************************/
int replay (char * name, int argc, char ** argv)
{
  if (argc < 1)
    {
      cout << "no schedule given" << endl << endl;
      printUsageReplay(name);
      return -1;
    }

  unsigned int      bound = 0;
  string            path2Schedule;

  for (int i = 0; i < argc; i++)
    {
      string arg(argv[i]);

      if (arg == "-v")
        {
          verbose = true;
        }
      else if (arg == "-k")
        {
          // throws std::invalid_argument
          bound = stoul((arg = argv[++i]), nullptr, 0);
        }
      else
        {
          path2Schedule = arg;
        }
    }

  /* create and parse schedule */
  Schedule schedule(path2Schedule);

  /* run given schedule */
  Machine machine(schedule.getSeed(), bound);

  return machine.replay(schedule);
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
    }

  /* found no command */
  printUsageMain(argv[0]);
  return -1;
}
