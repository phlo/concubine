/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef SHELL_HH_
#define SHELL_HH_

#include <sstream>
#include <vector>

namespace ConcuBinE::shell {

struct Output
{
  int exit;
  std::stringstream stdout, stderr;
};

// run command with given input (via stdin)
//
Output run (const std::vector<std::string> & command,
            const std::string & input = "");

} // namespace ConcuBinE::shell

#endif
