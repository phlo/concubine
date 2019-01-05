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
  string formula = "(exit)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", boolector.std_out);
}

TEST_F(BoolectorTest, unsat)
{
  string formula =
    "(set-logic QF_AUFBV)\n"
    "(declare-fun x1 () Bool)\n"
    "(declare-fun x2 () Bool)\n"
    "(assert (not x1))\n"
    "(assert (and x1 x2))\n"
    "(check-sat)\n"
    "(exit)\n";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", boolector.std_out);
}
