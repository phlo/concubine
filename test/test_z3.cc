#include <gtest/gtest.h>

#include <sstream>

#include "encoder.hh"
#include "parser.hh"
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

// TODO: remove
TEST_F(Z3Test, print_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  ProgramListPtr programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  EncoderPtr encoder = make_shared<SMTLibEncoderFunctional>(programs, 12);

  string formula = z3.build_formula(*encoder, constraints);

  ASSERT_TRUE(z3.sat(formula));

  cout << z3.std_out.str();
}
