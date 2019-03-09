#ifndef PARSER_HH_
#define PARSER_HH_

#include <string>
#include <fstream>

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
