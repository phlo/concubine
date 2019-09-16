#ifndef FS_HH_
#define FS_HH_

#include <filesystem>
#include <fstream>

// forward declarations
//
namespace ConcuBinE::smtlib {
  class Encoder;
  class Functional;
  class Relational;
}

namespace ConcuBinE::test::fs {

// return formula file extension
//
template <class Encoder>
inline std::string ext (const std::string & extension = "")
{
  if constexpr(std::is_base_of<smtlib::Encoder, Encoder>::value)
    {
      if constexpr(std::is_base_of<smtlib::Functional, Encoder>::value)
        return ".functional" + (extension.empty() ? ".smt2" : extension);
      else
        return ".relational" + (extension.empty() ? ".smt2" : extension);
    }
  else
    return extension.empty() ? ".btor2" : extension;
}

template <class Encoder>
inline std::string ext (const size_t threads,
                        const size_t bound,
                        const std::string & extension = "")
{
  return
    ".t" + std::to_string(threads) +
    ".k" + std::to_string(bound) +
    ext<Encoder>(extension);
}

// create temporary file (including directory structure)
//
inline std::filesystem::path mktmp (const std::filesystem::path & file = "",
                                    const std::string & extension = "")
{
  auto tmp = std::filesystem::temp_directory_path() / "concubine" / file;
  tmp += extension;
  std::filesystem::create_directories(tmp.parent_path());
  return tmp;
}

// read file
inline std::string read (const std::filesystem::path & file)
{
  std::ifstream ifs(file);
  std::string content((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  return content;
}

// write to file
//
inline void write (const std::filesystem::path & file, const std::string & data)
{
  if (!std::filesystem::exists(file))
    {
      std::ofstream ofs(file);
      ofs << data;
    }
}

// diff two files
//
inline bool diff (const std::filesystem::path & a,
                  const std::filesystem::path & b)
{
  std::ifstream ia(a);
  std::ifstream ib(b);

  std::istreambuf_iterator<char> ba(ia);
  std::istreambuf_iterator<char> bb(ib);
  std::istreambuf_iterator<char> end;

  while (ba != end && bb != end)
    {
      if (*ba != *bb)
        return true;

      ++ba;
      ++bb;
    }

  return !((ba == end) && (bb == end));
}

// update file if it differs
//
inline void update (const std::filesystem::path & file)
{
  auto tmp = mktmp(file);
  if (diff(tmp, file))
    std::filesystem::copy(
      tmp,
      file,
      std::filesystem::copy_options::overwrite_existing);
}

} // namespace ConcuBinE::test::fs

#endif
