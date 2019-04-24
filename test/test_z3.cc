#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "z3.hh"

using namespace std;

struct Z3Test : public ::testing::Test
{
  Z3              z3;
  EncoderPtr      encoder;
  ProgramListPtr  programs = make_shared<ProgramList>();
  SchedulePtr     schedule;
};

TEST_F(Z3Test, sat)
{
  string formula = "(assert true)(check-sat)";

  ASSERT_TRUE(z3.sat(formula));
}

TEST_F(Z3Test, unsat)
{
  string formula = "(assert false)(check-sat)";

  ASSERT_FALSE(z3.sat(formula));
}

TEST_F(Z3Test, solve_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = z3.solve(*encoder, constraints);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->size());

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(increment_0, schedule->programs->at(0)->path);
  ASSERT_EQ(increment_n, schedule->programs->at(1)->path);

  ASSERT_EQ(
    Schedule::Update_Map({
      {1, 0},
      {2, 1},
      {3, 0},
      {7, 1},
      {11, 0},
      {12, 1},
      {13, 0}
    }),
    schedule->thread_updates);
}

TEST_F(Z3Test, solve_cas)
{
  /* concurrent increment using CAS */
  string constraints;
  string increment = "data/increment.cas.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = z3.solve(*encoder, constraints);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->size());

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(increment, schedule->programs->at(0)->path);
  ASSERT_EQ(increment, schedule->programs->at(1)->path);

  ASSERT_EQ(
    Schedule::Update_Map({
      {1, 1},
      {2, 0},
      {3, 1}
    }),
    schedule->thread_updates);
}
