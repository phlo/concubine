/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef MARKDOWN_HH
#define MARKDOWN_HH

#include <iomanip>
#include <sstream>
#include <vector>

namespace ConcuBinE::test::md {

inline void table (const std::vector<std::string> & header,
                   const std::vector<std::vector<std::string>> & data,
                   std::ostream & os)
{
  const size_t cols = header.size();
  std::vector<size_t> widths(cols);

  // determine column size
  for (size_t i = 0; i < cols; i++)
    if (auto w = header[i].size(); w > widths[i])
      widths[i] = w;

  for (const auto & row : data)
    if (row.size() != cols)
      throw std::runtime_error("illegal row size");
    else
      for (size_t i = 0; i < cols; i++)
        if (auto w = row[i].size(); w > widths[i])
          widths[i] = w;

  // header
  os << '|';
  for (size_t i = 0; i < cols; i++)
    os << ' ' << std::left << std::setw(widths[i]) << header[i] << " |";
  os << '\n';

  // delimiter
  os << '|';
  for (size_t i = 0; i < cols; i++)
    os << ' ' << std::string(widths[i], '-') << " |";
  os << '\n';

  // data
  for (const auto & row : data)
    {
      os << '|';
      for (size_t i = 0; i < cols; i++)
        os << ' ' << std::left << std::setw(widths[i]) << row[i] << " |";
      os << '\n';
    }
}

inline std::string table (const std::vector<std::string> & header,
                          const std::vector<std::vector<std::string>> & data)
{
  std::ostringstream oss;
  table(header, data, oss);
  return oss.str();
}

} // namespace ConcuBinE::test:md

#endif
