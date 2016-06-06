#include <string>
#include <vector>
#include <iostream>
#include <stdexcept>

#include "parser.hh"
#include "machine.hh"

using namespace std;

/* global flags ***************************************************************/
bool verbose = false;

/* helper *********************************************************************/
void printUsage (char *); // shutup warnings
void printUsage (char * name)
{
  cout <<
  "usage: " << name << " [-v] [-s seed] [-k steps] source_file ...\n" <<
  "  -v            verbose schedule output\n" <<
  "  -s seed       random number generator's seed\n" <<
  "  -k steps      sets bound for machine to execute a maximum of k steps\n" <<
  "  source_file   one ore more source files, each being executed as a separate thread\n";
}

/*******************************************************************************
 * main
 * TODO: error handling!!!
 ******************************************************************************/
int main (int argc, char **argv)
{
  /* parse command line */
  if (argc < 2)
    {
      cout << "invalid number of arguments" << endl << endl;
      printUsage(argv[0]);
      return -1;
    }

  unsigned int      seed = time(NULL);
  unsigned int      steps = 0;
  vector<Program *> threads;

  for (int i = 1; i < argc; i++)
    {
      string arg(argv[i]);

      if (arg == "-h")
        {
          printUsage(argv[0]);
          return 0;
        }
      if (arg == "-v")
        {
          verbose = true;
        }
      else if (arg == "-s")
        {
          seed = stoul((arg = argv[++i]), nullptr, 0); // throws std::invalid_argument
        }
      else if (arg == "-k")
        {
          steps = stoul((arg = argv[++i]), nullptr, 0); // throws std::invalid_argument
        }
      else
        {
          threads.push_back(new Program(arg));
        }
    }
  if (threads.empty())
    {
      cout << "got nothing to run" << endl;
      printUsage(argv[0]);
      return -1;
    }

  /* run schedule with given seed */
  Machine machine(seed, steps);
  for (auto p : threads)
    machine.createThread(*p);

  return machine.simulate();
}
