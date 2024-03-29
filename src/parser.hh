/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef PARSER_HH_
#define PARSER_HH_

#include <fstream>

namespace ConcuBinE {

// error reporting helper
//
inline void parser_error (const std::string & file,
                          const size_t line,
                          const std::string && msg)
{
  throw std::runtime_error(file + ":" + std::to_string(line) + ": " + msg);
}

// file parsing helper
//
template <class T>
inline T create_from_file (const std::string & path)
{
  std::ifstream file(path);

  if (file)
    return T (file, path);
  else
    throw std::runtime_error(path + " not found");
}

} // namespace ConcuBinE

#endif
