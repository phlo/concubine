#include <gtest/gtest.h>

#include <sstream>

#include "cvc4.hh"
#include "streamredirecter.hh"

using namespace std;

struct CVC4Test : public ::testing::Test
{
  CVC4 cvc4;
};

TEST_F(CVC4Test, sat)
{
  string formula = "(set-logic QF_AUFBV)(assert true)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(cvc4.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", cvc4.std_out.str());
}

TEST_F(CVC4Test, unsat)
{
  string formula = "(set-logic QF_AUFBV)(assert false)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(cvc4.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", cvc4.std_out.str());
}
