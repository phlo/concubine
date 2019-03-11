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

/* parse **********************************************************************/
TEST_F(ScheduleTest, parse)
{
  schedule =
    SchedulePtr(
      create_from_file<Schedule>("data/increment.cas.t2.k16.schedule"));

  ASSERT_EQ(0, schedule->seed);
  ASSERT_EQ(2, schedule->programs.size());
  ASSERT_EQ(16, schedule->size());

  ASSERT_EQ(0, schedule->at(0));
  ASSERT_EQ(1, schedule->at(1));
  ASSERT_EQ(1, schedule->at(2));
  ASSERT_EQ(0, schedule->at(3));
  ASSERT_EQ(0, schedule->at(4));
  ASSERT_EQ(0, schedule->at(5));
  ASSERT_EQ(1, schedule->at(6));
  ASSERT_EQ(0, schedule->at(7));
  ASSERT_EQ(0, schedule->at(8));
  ASSERT_EQ(1, schedule->at(9));
  ASSERT_EQ(1, schedule->at(10));
  ASSERT_EQ(0, schedule->at(11));
  ASSERT_EQ(0, schedule->at(12));
  ASSERT_EQ(0, schedule->at(13));
  ASSERT_EQ(0, schedule->at(14));
  ASSERT_EQ(1, schedule->at(15));
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
  string dummy_file = "data/test.schedule";

  istringstream inbuf;

  /* no seed */
  inbuf.str(
    "0 = data/increment.checker.asm\n"
    "1 = data/increment.asm\n"
    "0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":3: expected thread id 2", e.what());
    }

  /* no program */
  inbuf.str(
    "seed = 0\n"
    "0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":2: missing threads", e.what());
    }

  /* illegal initial thread id (must start with 0) */
  inbuf.str(
    "1 = data/increment.asm\n"
    "seed = 0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":1: thread id must start from zero", e.what());
    }

  /* illegal thread id (missing 1) */
  inbuf.str(
    "0 = data/increment.asm\n"
    "2 = data/increment.asm\n"
    "seed = 0\n"
    "0\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":2: expected thread id 1", e.what());
    }

  /* illegal seed (not an int) */
  inbuf.str(
    "0 = data/increment.asm\n"
    "seed = wrong\n"
    "0\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":2: illegal seed [wrong]", e.what());
    }

  /* illegal thread id (not an int) */
  inbuf.str(
    "wrong = data/increment.asm\n"
    "seed = 0\n"
    "0\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":1: illegal thread id [wrong]", e.what());
    }

  /* illegal thread id scheduled (unknown id) */
  inbuf.str(
    "0 = data/increment.asm\n"
    "seed = 0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":3: unknown thread id [1]", e.what());
    }

  /* illegal thread id (not an int) */
  inbuf.str(
    "0 = data/increment.asm\n"
    "seed = 0\n"
    "wrong\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":3: illegal thread id [wrong]", e.what());
    }
}
