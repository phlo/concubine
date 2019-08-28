#ifndef FILESYSTEM_HH_
#define FILESYSTEM_HH_

#include <filesystem>
#include <fstream>

namespace ConcuBinE::test::fs {

// create temporary directory
//
inline std::filesystem::path mktmp (const std::filesystem::path & file)
{
  auto tmp = std::filesystem::temp_directory_path() / "concubine" / file;

  std::filesystem::create_directories(tmp.parent_path());

  return tmp;
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

} // namespace ConcuBinE::test::fs

#endif
