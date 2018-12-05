#ifndef STREAMREDIRECTER_HH_
#define STREAMREDIRECTER_HH_

#include <ostream>

class StreamRedirecter
{
  std::basic_ios<char> &  src;
  std::basic_ios<char> &  dest;

  std::streambuf * const  src_rdbuf;

public:

  StreamRedirecter (std::basic_ios<char> & from, std::basic_ios<char> & to) :
    src(from),
    dest(to),
    src_rdbuf(src.rdbuf())
    {}

  ~StreamRedirecter () { src.rdbuf(src_rdbuf); }

  void start () { src.rdbuf(dest.rdbuf()); }

  void stop () { src.rdbuf(src_rdbuf); }
};

#endif
