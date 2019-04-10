#include <gtest/gtest.h>

#include "boolector.hh"
#include "encoder.hh"
#include "parser.hh"
#include "streamredirecter.hh"

using namespace std;

struct BoolectorTest : public ::testing::Test
{
  Boolector       boolector;
  EncoderPtr      encoder;
  ProgramListPtr  programs = make_shared<ProgramList>();
  SchedulePtr     schedule;
};

TEST_F(BoolectorTest, sat)
{
  string formula = "(assert true)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", boolector.std_out.str());
}

TEST_F(BoolectorTest, unsat)
{
  string formula = "(assert false)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", boolector.std_out.str());
}

TEST_F(BoolectorTest, solve_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 12);

  schedule = boolector.solve(*encoder, constraints);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(12, schedule->size());

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(increment_0, schedule->programs->at(0)->path);
  ASSERT_EQ(increment_n, schedule->programs->at(1)->path);

  ASSERT_EQ(
    vector<word>({0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1}),
    schedule->scheduled);

  // redirecter.stop();

  ASSERT_EQ("unsat\n", boolector.std_out.str());
}

TEST_F(BoolectorTest, solve_missing_model)
{
  programs = make_shared<ProgramList>();

  programs->push_back(make_shared<Program>());

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 1);

  string constraints;

  boolector.solve(*encoder, constraints);
}
