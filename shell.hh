#ifndef SHELL_HH_
#define SHELL_HH_

#include <sstream>

namespace ConcuBinE {

//==============================================================================
// Shell
//==============================================================================

class Shell
{
  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // last exit code ($?)
  //
  int exit_code;

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

public:

  // returns last exit code (like $?)
  //
  int last_exit_code ();

  // runs shell command and returns it's output
  //
  std::stringstream run (const std::string & input);

  // pipes input into shell command and returns it's output
  //
  std::stringstream run (const std::string & cmd, const std::string & input);
};

} // namespace ConcuBinE

#endif
