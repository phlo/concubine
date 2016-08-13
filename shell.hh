#ifndef SHELL_HH_
#define SHELL_HH_

#include <memory>
#include <string>

using namespace std;

/*******************************************************************************
 * Shell
*******************************************************************************/
class Shell
{
  /* last exit code ($?) */
  int exitCode;

public:
  
  /* returns last exit code (like $?) */
  int lastExitCode (void);

  /* run shell command and returns it's output */
  string run (string);

  /* pipe input into shell command and return it's output */
  string run (string, string &);
};

/*******************************************************************************
 * ShellPtr
*******************************************************************************/
typedef shared_ptr<Shell> ShellPtr;

#endif
