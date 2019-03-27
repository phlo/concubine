#include <gtest/gtest.h>

#include "parser.hh"
#include "schedule.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ScheduleTest : public ::testing::Test
{
  string dummy_file = "dummy.schedule";

  string program = "data/increment.cas.asm";

  SchedulePtr schedule = SchedulePtr(new Schedule());
};

/* parse **********************************************************************/
TEST_F(ScheduleTest, parse)
{
  schedule = create_from_file<Schedule>("data/increment.cas.t2.k16.schedule");

  ASSERT_EQ(schedule->path, "data/increment.cas.t2.k16.schedule");

  ASSERT_EQ(16, schedule->bound);

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(program, schedule->programs->at(0)->path);
  ASSERT_EQ(program, schedule->programs->at(1)->path);

  ASSERT_EQ(0, schedule->threads.at(0));
  ASSERT_EQ(1, schedule->threads.at(1));
  ASSERT_EQ(1, schedule->threads.at(2));
  ASSERT_EQ(0, schedule->threads.at(3));
  ASSERT_EQ(0, schedule->threads.at(4));
  ASSERT_EQ(0, schedule->threads.at(5));
  ASSERT_EQ(1, schedule->threads.at(6));
  ASSERT_EQ(0, schedule->threads.at(7));
  ASSERT_EQ(0, schedule->threads.at(8));
  ASSERT_EQ(1, schedule->threads.at(9));
  ASSERT_EQ(1, schedule->threads.at(10));
  ASSERT_EQ(0, schedule->threads.at(11));
  ASSERT_EQ(0, schedule->threads.at(12));
  ASSERT_EQ(0, schedule->threads.at(13));
  ASSERT_EQ(0, schedule->threads.at(14));
  ASSERT_EQ(1, schedule->threads.at(15));
}

/* parse_empty_line ***********************************************************/
TEST_F(ScheduleTest, parse_empty_line)
{
  istringstream inbuf(
    "0 = " + program + "\n"
    "\n"
    "seed = 0\n"
    "\n"
    "0\n");

  schedule = SchedulePtr(new Schedule(inbuf, dummy_file));

  ASSERT_EQ(1, schedule->programs->size());
  ASSERT_EQ(program, schedule->programs->at(0)->path);
  ASSERT_EQ(0, schedule->threads.at(0));
}

/* parse_file_not_found *******************************************************/
TEST_F(ScheduleTest, parse_file_not_found)
{
  try
    {
      schedule = create_from_file<Schedule>("file_not_found");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("file_not_found not found", e.what());
    }
}

/* parse_illegal_schedule *****************************************************/
TEST_F(ScheduleTest, parse_illegal_schedule)
{
  istringstream inbuf;

  /* no seed */
  inbuf.str(
    "0 = " + program + "\n"
    "1 = " + program + "\n"
    "0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
      FAIL() << "should throw an exception";
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
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":2: missing threads", e.what());
    }

  /* program not found */
  inbuf.str(
    "0 = program.asm\n"
    "seed = 0\n"
    "0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":1: program.asm not found", e.what());
    }

  /* missing thread id */
  inbuf.str(
    program + "\n"
    "seed = 0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_file + ":1: illegal thread id [" + program + "]",
        e.what());
    }

  /* illegal initial thread id (must start with 0) */
  inbuf.str(
    "1 = " + program + "\n"
    "seed = 0\n"
    "1\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":1: thread id must start from zero", e.what());
    }

  /* illegal thread id (missing 1) */
  inbuf.str(
    "0 = " + program + "\n"
    "2 = " + program + "\n"
    "seed = 0\n"
    "0\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_file));
      FAIL() << "should throw an exception";
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
      FAIL() << "should throw an exception";
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
      FAIL() << "should throw an exception";
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
      FAIL() << "should throw an exception";
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
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_file + ":3: illegal thread id [wrong]", e.what());
    }
}

// std::string print (void)
TEST_F(ScheduleTest, print)
{
  schedule = create_from_file<Schedule>("data/increment.cas.t2.k16.schedule");

  ASSERT_EQ("", schedule->print());
}
