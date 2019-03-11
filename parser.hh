#ifndef PARSER_HH_
#define PARSER_HH_

#include <string>
#include <fstream>

/* error reporting helper *****************************************************/
inline
void parser_error (std::string & file, unsigned long line, std::string && msg)
{
  throw std::runtime_error(file + ":" + std::to_string(line) + ": " + msg);
}

/* file parsing helper ********************************************************/
template <typename T>
T * create_from_file (std::string path)
{
  T * result;

  std::ifstream file(path);

  if (file.is_open())
    {
      result = new T(file, path);
      file.close();
    }
  else
    throw std::runtime_error(path + " not found");

  return result;
}

#endif
