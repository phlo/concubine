#include <gtest/gtest.h>

#include <sstream>

#include "boolector.hh"
#include "streamredirecter.hh"

using namespace std;

struct BoolectorTest : public ::testing::Test
{
  Boolector boolector;
};

TEST_F(BoolectorTest, sat)
{
  string formula = "(assert true)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", boolector.std_out);
}

TEST_F(BoolectorTest, unsat)
{
  string formula = "(assert false)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", boolector.std_out);
}
