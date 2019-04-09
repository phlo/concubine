#ifndef SHELL_HH_
#define SHELL_HH_

#include <memory>

/*******************************************************************************
 * Shell
*******************************************************************************/
class Shell
{
  /* last exit code ($?) */
  int exit_code;

public:

  /* returns last exit code (like $?) */
  int last_exit_code (void);

  /* runs shell command and returns it's output */
  std::stringstream run (std::string);

  /* pipes input into shell command and returns it's output */
  std::stringstream run (std::string, std::string &);
};

/*******************************************************************************
 * ShellPtr
*******************************************************************************/
typedef std::shared_ptr<Shell> ShellPtr;

#endif
