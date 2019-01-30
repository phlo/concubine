#include <gtest/gtest.h>

#include "btor2.hh"

using namespace std;

// inline std::string comment (std::string)
TEST(Btor2Test, comment)
{
  ASSERT_EQ("; foo", btor2::comment("foo"));
}

// inline std::string comment_section (std::string)
TEST(Btor2Test, comment_section)
{
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; foo\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    btor2::comment_section("foo"));
}

// inline std::string declare_subsection (std::string, std::string, std::string)
TEST(Btor2Test, comment_subsection)
{
  ASSERT_EQ(
    "; foo ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    btor2::comment_subsection("foo"));
}

// inline std::string declare_sort (std::string, std::string)
TEST(Btor2Test, declare_sort)
{
  ASSERT_EQ("1 sort bitvec 1\n", btor2::declare_sort("1", "1"));
  ASSERT_EQ("2 sort bitvec 16\n", btor2::declare_sort("2", "16"));
  ASSERT_EQ("3 sort bitvec 32\n", btor2::declare_sort("3", "32"));
}

// inline std::string declare_array (std::string, std::string, std::string)
TEST(Btor2Test, declare_array)
{
  ASSERT_EQ("1 sort array 2 2\n", btor2::declare_array("1", "2", "2"));
  ASSERT_EQ("2 sort array 16 16\n", btor2::declare_array("2", "16", "16"));
  ASSERT_EQ("3 sort array 32 32\n", btor2::declare_array("3", "32", "32"));
}

// inline std::string constd (std::string, std::string, std::string)
TEST(Btor2Test, constd)
{
  ASSERT_EQ("12 constd 2 2\n", btor2::constd("12", "2", "2"));
  ASSERT_EQ("13 constd 3 3\n", btor2::constd("13", "3", "3"));
  ASSERT_EQ("14 constd 4 4\n", btor2::constd("14", "4", "4"));

  /* zero one */
  ASSERT_EQ("1 zero 1\n", btor2::constd("1", "1", "0"));
  ASSERT_EQ("2 one 1\n", btor2::constd("2", "1", "1"));
}

// inline std::string input (std::string, std::string)
TEST(Btor2Test, input)
{
  ASSERT_EQ("11 input 1\n", btor2::input("11", "1"));
  ASSERT_EQ("12 input 2\n", btor2::input("12", "2"));
  ASSERT_EQ("13 input 3\n", btor2::input("13", "3"));
}

// inline std::string state (std::string, std::string)
TEST(Btor2Test, state)
{
  ASSERT_EQ("11 state 1\n", btor2::state("11", "1"));
  ASSERT_EQ("12 state 2\n", btor2::state("12", "2"));
  ASSERT_EQ("13 state 3\n", btor2::state("13", "3"));
}

// inline std::string init (std::string, std::string, std::string, std::string)
TEST(Btor2Test, init)
{
  ASSERT_EQ("11 init 1 2 3\n", btor2::init("11", "1", "2", "3"));
  ASSERT_EQ("12 init 4 5 6\n", btor2::init("12", "4", "5", "6"));
  ASSERT_EQ("13 init 7 8 9\n", btor2::init("13", "7", "8", "9"));
}

// inline std::string next (std::string, std::string, std::string, std::string)
TEST(Btor2Test, next)
{
  ASSERT_EQ("11 next 1 2 3\n", btor2::next("11", "1", "2", "3"));
  ASSERT_EQ("12 next 4 5 6\n", btor2::next("12", "4", "5", "6"));
  ASSERT_EQ("13 next 7 8 9\n", btor2::next("13", "7", "8", "9"));
}

// inline std::string constraint (std::string, std::string)
TEST(Btor2Test, constraint)
{
  ASSERT_EQ("11 constraint 1\n", btor2::constraint("11", "1"));
  ASSERT_EQ("12 constraint 2\n", btor2::constraint("12", "2"));
  ASSERT_EQ("13 constraint 3\n", btor2::constraint("13", "3"));
}

// inline std::string bad (std::string, std::string)
TEST(Btor2Test, bad)
{
  ASSERT_EQ("11 bad 1\n", btor2::bad("11", "1"));
  ASSERT_EQ("12 bad 2\n", btor2::bad("12", "2"));
  ASSERT_EQ("13 bad 3\n", btor2::bad("13", "3"));
}

// inline std::string fair (std::string, std::string)
TEST(Btor2Test, fair)
{
  ASSERT_EQ("11 fair 1\n", btor2::fair("11", "1"));
  ASSERT_EQ("12 fair 2\n", btor2::fair("12", "2"));
  ASSERT_EQ("13 fair 3\n", btor2::fair("13", "3"));
}

// inline std::string output (std::string, std::string)
TEST(Btor2Test, output)
{
  ASSERT_EQ("11 output 1\n", btor2::output("11", "1"));
  ASSERT_EQ("12 output 2\n", btor2::output("12", "2"));
  ASSERT_EQ("13 output 3\n", btor2::output("13", "3"));
}

// inline std::string justice (std::string, std::string, vector<std::string>)
TEST(Btor2Test, justice)
{
  ASSERT_EQ("11 justice 1 1\n", btor2::justice("11", "1", {"1"}));
  ASSERT_EQ("12 justice 2 1 2\n", btor2::justice("12", "2", {"1", "2"}));
  ASSERT_EQ("13 justice 3 1 2 3\n", btor2::justice("13", "3", {"1", "2", "3"}));
}

// inline std::string sext (std::string, std::string, std::string)
TEST(Btor2Test, sext)
{
  ASSERT_EQ("11 sext 1 2\n", btor2::sext("11", "1", "2"));
  ASSERT_EQ("12 sext 2 3\n", btor2::sext("12", "2", "3"));
  ASSERT_EQ("13 sext 3 4\n", btor2::sext("13", "3", "4"));
}

// inline std::string uext (std::string, std::string, std::string)
TEST(Btor2Test, uext)
{
  ASSERT_EQ("11 uext 1 2\n", btor2::uext("11", "1", "2"));
  ASSERT_EQ("12 uext 2 3\n", btor2::uext("12", "2", "3"));
  ASSERT_EQ("13 uext 3 4\n", btor2::uext("13", "3", "4"));
}

// inline std::string slice (std::string, std::string, std::string, std::string)
TEST(Btor2Test, slice)
{
  ASSERT_EQ("11 slice 1 3 2\n", btor2::slice("11", "1", "3", "2"));
  ASSERT_EQ("12 slice 2 4 3\n", btor2::slice("12", "2", "4", "3"));
  ASSERT_EQ("13 slice 3 5 4\n", btor2::slice("13", "3", "5", "4"));
}

// inline std::string lnot (std::string, std::string, std::string)
TEST(Btor2Test, lnot)
{
  ASSERT_EQ("11 not 1 2\n", btor2::lnot("11", "1", "2"));
  ASSERT_EQ("12 not 2 3\n", btor2::lnot("12", "2", "3"));
  ASSERT_EQ("13 not 3 4\n", btor2::lnot("13", "3", "4"));
}
