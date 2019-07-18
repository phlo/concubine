#include <gtest/gtest.h>

#include "mmap.hh"

#include "parser.hh"

namespace ConcuBinE::test {

//==============================================================================
// MMap tests
//==============================================================================

struct MMap : public ::testing::Test
{
  std::string path = "dummy.mmap";

  ConcuBinE::MMap mmap;

  void create_mmap (std::string code)
    {
      std::istringstream inbuf {code};
      mmap = ConcuBinE::MMap(inbuf, path);
    }
};

// construction ================================================================

TEST_F(MMap, construction)
{
  create_mmap("0 0\n");

  ConcuBinE::MMap & m1 = mmap;
  ASSERT_FALSE(m1.empty());

  // copy construction
  ConcuBinE::MMap m2 (m1);
  ASSERT_NE(&m1[0], &m2[0]);
  ASSERT_EQ(m1, m2);

  const auto * ptr = &m1[0];

  // std::move construction
  ConcuBinE::MMap m3 (std::move(m1));
  ASSERT_TRUE(m1.empty());
  ASSERT_EQ(m2, m3);
  ASSERT_EQ(ptr, &m3[0]);

  // copy assignment
  m1 = m2;
  ASSERT_EQ(m1, m3);
  ASSERT_NE(&m1[0], &m2[0]);
  ASSERT_NE(&m1[0], &m3[0]);

  // std::move assignment
  m2 = std::move(m3);
  ASSERT_TRUE(m3.empty());
  ASSERT_EQ(m1, m2);
  ASSERT_EQ(ptr, &m2[0]);
}

// parser ======================================================================

TEST_F(MMap, parse)
{
  create_mmap(
    "0 0\n"
    "1 1\n"
    "2 2\n"
  );

  ASSERT_EQ(path, mmap.path);
  ASSERT_EQ(3, mmap.size());

  for (word_t i = 0; i < mmap.size(); i++)
    ASSERT_EQ(i, mmap.at(i));
}

TEST_F(MMap, parse_comment)
{
  create_mmap(
    "# a comment\n"
    "0 0\n"
    "# another comment\n"
    "1 1\n"
  );

  ASSERT_EQ(path, mmap.path);
  ASSERT_EQ(2, mmap.size());

  for (word_t i = 0; i < mmap.size(); i++)
    ASSERT_EQ(i, mmap.at(i));
}

TEST_F(MMap, parse_empty_line)
{
  create_mmap(
    "0 0\n"
    "\n"
    "1 1\n"
  );

  ASSERT_EQ(path, mmap.path);
  ASSERT_EQ(2, mmap.size());

  for (word_t i = 0; i < mmap.size(); i++)
    ASSERT_EQ(i, mmap.at(i));
}

TEST_F(MMap, parse_file_not_found)
{
  try
    {
      mmap = create_from_file<ConcuBinE::MMap>("file");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_STREQ("file not found", e.what());
    }
}

TEST_F(MMap, parse_illegal_address)
{
  try
    {
      create_mmap("ILLEGAL 0\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: illegal address [ILLEGAL]", e.what());
    }
}

TEST_F(MMap, parse_illegal_value)
{
  try
    {
      create_mmap("0 ILLEGAL\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: illegal value [ILLEGAL]", e.what());
    }
}

// MMap::print =================================================================

TEST_F(MMap, print)
{
  std::string expected =
    "0 0\n"
    "1 1\n"
    "2 2\n";

  create_mmap(expected);
  ASSERT_EQ(expected, mmap.print());
}

} // namespace ConcuBinE::test
