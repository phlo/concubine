#ifndef PARSER_HH_
#define PARSER_HH_

#include <fstream>

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

#endif
