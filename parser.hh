#ifndef PARSER_HH_
#define PARSER_HH_

#include <fstream>
#include <memory>
#include <string>

/* error reporting helper *****************************************************/
inline
void parser_error (std::string file, size_t line, std::string && msg)
{
  throw std::runtime_error(file + ":" + std::to_string(line) + ": " + msg);
}

/* file parsing helper ********************************************************/
template <typename T>
std::shared_ptr<T> create_from_file (std::string path)
{
  std::shared_ptr<T> result;

  std::ifstream file(path);

  if (file.is_open())
    {
      result.reset(new T(file, path));
      file.close();
    }
  else
    throw std::runtime_error(path + " not found");

  return result;
}

#endif
