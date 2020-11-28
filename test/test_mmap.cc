/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include <gtest/gtest.h>

#include "mmap.hh"

#include "parser.hh"

namespace ConcuBinE::test {

//==============================================================================
// MMap tests
//==============================================================================

const std::string path = "dummy.mmap";

inline MMap mmap (const std::string & code)
{
  std::istringstream inbuf(code);
  return MMap(inbuf, path);
}

// construction ================================================================

TEST(MMap, construction)
{
  auto m0 = mmap("0 0\n");

  // copy construction
  MMap m1(m0);
  ASSERT_NE(&m0[0], &m1[0]);
  ASSERT_EQ(m0, m1);

  const auto * ptr = &m0[0];

  // std::move construction
  MMap m2(std::move(m0));
  ASSERT_TRUE(m0.empty());
  ASSERT_EQ(m1, m2);
  ASSERT_EQ(ptr, &m2[0]);

  // copy assignment
  m0 = m1;
  ASSERT_EQ(m0, m2);
  ASSERT_NE(&m0[0], &m1[0]);
  ASSERT_NE(&m0[0], &m2[0]);

  // std::move assignment
  m1 = std::move(m2);
  ASSERT_TRUE(m2.empty());
  ASSERT_EQ(m0, m1);
  ASSERT_EQ(ptr, &m1[0]);
}

// parser ======================================================================

TEST(MMap, parse)
{
  auto m = mmap(
    "0 0\n"
    "1 1\n"
    "2 2\n");

  ASSERT_EQ(path, m.path);
  ASSERT_EQ(3, m.size());

  for (word_t i = 0; i < m.size(); i++)
    ASSERT_EQ(i, m.at(i));
}

TEST(MMap, parse_comment)
{
  auto m = mmap(
    "# a comment\n"
    "0 0\n"
    "# another comment\n"
    "1 1\n");

  ASSERT_EQ(path, m.path);
  ASSERT_EQ(2, m.size());

  for (word_t i = 0; i < m.size(); i++)
    ASSERT_EQ(i, m.at(i));
}

TEST(MMap, parse_empty_line)
{
  auto m = mmap(
    "0 0\n"
    "\n"
    "1 1\n");

  ASSERT_EQ(path, m.path);
  ASSERT_EQ(2, m.size());

  for (word_t i = 0; i < m.size(); i++)
    ASSERT_EQ(i, m.at(i));
}

TEST(MMap, parse_file_not_found)
{
  try
    {
      auto m = create_from_file<MMap>("file");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_STREQ("file not found", e.what());
    }
}

TEST(MMap, parse_illegal_address)
{
  try
    {
      auto m = mmap("ILLEGAL 0\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: illegal address [ILLEGAL]", e.what());
    }
}

TEST(MMap, parse_illegal_value)
{
  try
    {
      auto m = mmap("0 ILLEGAL\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: illegal value [ILLEGAL]", e.what());
    }
}

// MMap::print =================================================================

TEST(MMap, print)
{
  const std::string expected =
    "0 0\n"
    "1 1\n"
    "2 2\n";

  auto m = mmap(expected);
  ASSERT_EQ(expected, m.print());
}

} // namespace ConcuBinE::test
