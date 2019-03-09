#include <gtest/gtest.h>

#include "parser.hh"
#include "schedule.hh"
#include "streamredirecter.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ScheduleTest : public ::testing::Test
{
  SchedulePtr schedule = SchedulePtr(new Schedule());
};

/* add_thread *****************************************************************/
TEST_F(ScheduleTest, add_thread)
{
  schedule->add(0);
  ASSERT_EQ(0, schedule->at(0));
  ASSERT_EQ(1, schedule->size());

  schedule->add(1);
  ASSERT_EQ(1, schedule->at(1));
  ASSERT_EQ(2, schedule->size());
}

/* add_program ****************************************************************/
TEST_F(ScheduleTest, add_program)
{
  schedule->add(0, ProgramPtr(create_from_file<Program>("data/increment.asm")));
  ASSERT_EQ(1, schedule->programs.size());

  schedule->add(2, ProgramPtr(create_from_file<Program>("data/increment.asm")));
  ASSERT_EQ(3, schedule->programs.size());
  ASSERT_EQ(nullptr, schedule->programs[1]);
}

/* parse **********************************************************************/
TEST_F(ScheduleTest, parse)
{
  schedule =
    SchedulePtr(create_from_file<Schedule>("data/increment.invalid.schedule"));

  ASSERT_EQ(0, schedule->seed);
  ASSERT_EQ(3, schedule->programs.size());
  ASSERT_EQ(13, schedule->size());
}

/* parse_file_not_found *******************************************************/
TEST_F(ScheduleTest, parse_file_not_found)
{
  try
    {
      schedule = SchedulePtr(create_from_file<Schedule>("file_not_found"));
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("file_not_found not found", e.what());
    }
}

/* parse_illegal_schedule *****************************************************/
TEST_F(ScheduleTest, parse_illegal_schedule)
{
  string dummy_file = "data/increment.asm";

  /* no seed */
  istringstream inbuf(" \
    0 = data/increment.checker.asm \
    1 = data/increment.asm \
    0 \
    1 \
    ");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("'=' expected", e.what());
    }

  /* no program */
  inbuf.str(" \
    seed = 0 \
    0 \
    1 \
    ");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("missing threads", e.what());
    }

  /* illegal seed (not an int) */
  inbuf.str(" \
    0 = data/increment.asm \
    seed = wrong \
    0 \
    ");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("illegal seed [wrong]", e.what());
    }

  /* illegal thread id (unknown id) */
  inbuf.str(" \
    1 = data/increment.asm \
    seed = 0 \
    0 \
    ");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("unknown thread id", e.what());
    }

  /* illegal thread id (not an int) */
  inbuf.str(" \
    wrong = data/increment.asm \
    seed = 0 \
    0 \
    ");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("illegal thread id [wrong]", e.what());
    }

  /* illegal thread id (not an int) */
  inbuf.str(" \
    1 = data/increment.asm \
    seed = 0 \
    wrong \
    ");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("illegal thread id [wrong]", e.what());
    }
}
