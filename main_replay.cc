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
  "usage: " << name << " [-v] [-k steps] schedule_file\n" <<
  "  -v            verbose schedule output\n" <<
  "  -k steps       sets bound for machine to execute a maximum of k steps\n" <<
  "  schedule_file  one ore more source files, each being executed as a separate thread\n";
}

/*******************************************************************************
 * main
 ******************************************************************************/
int main (int argc, char **argv)
{
  /* parse command line */
  if (argc < 2 || argc > 5)
    {
      cout << "invalid number of arguments" << endl << endl;
      printUsage(argv[0]);
      return -1;
    }

  unsigned int      steps = 0;
  string            path2Schedule;

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
      else if (arg == "-k")
        {
          steps = stoul((arg = argv[++i]), nullptr, 0); // throws std::invalid_argument
        }
      else
        {
          path2Schedule = arg;
        }
    }

  /* create and parse schedule */
  Schedule schedule(path2Schedule);

  /* run given schedule */
  Machine machine(schedule.getSeed(), steps);

  return machine.replay(schedule);
}
