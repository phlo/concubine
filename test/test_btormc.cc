#include <gtest/gtest.h>

#include <sstream>

#include "btormc.hh"
#include "streamredirecter.hh"

using namespace std;

struct BtorMCTest : public ::testing::Test
{
  BtorMC btormc;
};

TEST_F(BtorMCTest, sat)
{
  string formula =
    "1 sort bitvec 1\n"
    "2 state 1 x\n"
    "3 bad 2\n";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(btormc.sat(formula));

  redirecter.stop();

  ASSERT_EQ(
    "sat\n"
    "b0 \n"
    "#0\n"
    "0 1 x#0\n"
    "@0\n"
    ".\n",
    btormc.std_out);
}

TEST_F(BtorMCTest, unsat)
{
  string formula =
    "1 sort bitvec 1\n"
    "2 state 1 x\n";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(btormc.sat(formula));

  redirecter.stop();

  ASSERT_EQ("", btormc.std_out);
}
