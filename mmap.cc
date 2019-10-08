#include "mmap.hh"

#include <sstream>
#include <iostream>

#include "parser.hh"

namespace ConcuBinE {

//==============================================================================
// MMap
//==============================================================================

//------------------------------------------------------------------------------
// public constructors
//------------------------------------------------------------------------------

MMap::MMap (std::istream & f, const std::string & p) : path(p)
{
  size_t line_num = 1;
  for (std::string line_buf; std::getline(f, line_buf); line_num++)
    {
      // skip empty lines
      if (line_buf.empty())
        continue;

      std::istringstream line(line_buf);

      // skip comments
      if (line_buf[line_buf.find_first_not_of(" \t")] == '#')
        continue;

      word_t address;

      if (!(line >> address))
        {
          line.clear();

          std::string token;

          if (!(line >> token))
            parser_error(path, line_num, "missing address");

          parser_error(path, line_num, "illegal address [" + token + "]");
        }

      word_t value;

      if (!(line >> value))
        {
          line.clear();

          std::string token;

          if (!(line >> token))
            parser_error(path, line_num, "missing value");

          parser_error(path, line_num, "illegal value [" + token + "]");
        }

      emplace(address, value);
    }
}

//------------------------------------------------------------------------------
// public member functions
//------------------------------------------------------------------------------

// MMap::print -----------------------------------------------------------------

std::string MMap::print () const
{
  std::ostringstream ss;

  for (const auto & [adr, val] : *this)
    ss << adr << ' ' << val << eol;

  return ss.str();
}

} // namespace ConcuBinE
