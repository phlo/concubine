#include <gtest/gtest.h>

#include <fstream>
#include <string>

#include "smtlib.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
// struct EncoderTest : public ::testing::Test
// {
  // ProgramList     programs;
  // SMTLibEncoder   encoder;
//
  // EncoderTest () : programs(), encoder(programs, 0) {};
// };

TEST(SMTLibTest, expr)
{
  const char * expected = "(x1 x2 x3)";

  ASSERT_STREQ(expected, smtlib::expr({"x1", "x2", "x3"}).c_str());
}

/* collectPredecessors ********************************************************/
TEST(SMTLibTest, cardinality_exactly_one_naive)
{
  const char * expected =
    "(or (not x1) (not x2))\n"
    "(or (not x1) (not x3))\n"
    "(or (not x2) (not x3))\n";

  assert(false);
  ASSERT_STREQ(expected, smtlib::cardinality_exactly_one_naive({"x1", "x2", "x3"}).c_str());
}
