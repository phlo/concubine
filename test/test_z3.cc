#include <gtest/gtest.h>

#include <sstream>

#include "streamredirecter.hh"
#include "z3.hh"

using namespace std;

struct Z3Test : public ::testing::Test
{
  Z3 z3;
};

TEST_F(Z3Test, sat)
{
  string formula = "(assert true)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(z3.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n\"\"\n", z3.std_out.str());
}

TEST_F(Z3Test, unsat)
{
  string formula = "(assert false)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(z3.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", z3.std_out.str());
}
