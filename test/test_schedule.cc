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
  Schedule schedule;
};

/* addThread ******************************************************************/
TEST_F(ScheduleTest, addThread)
{
  schedule.add(0);
  ASSERT_EQ(0, schedule[0]);
  ASSERT_EQ(1, schedule.size());

  schedule.add(1);
  ASSERT_EQ(1, schedule[1]);
  ASSERT_EQ(2, schedule.size());
}

/* addProgram *****************************************************************/
TEST_F(ScheduleTest, addProgram)
{
  schedule.add(0, make_shared<Program>("data/increment.asm"));
  ASSERT_EQ(1, schedule.programs.size());

  schedule.add(2, make_shared<Program>("data/increment.asm"));
  ASSERT_EQ(3, schedule.programs.size());
  ASSERT_EQ(nullptr, schedule.programs[1]);
}

/* parse **********************************************************************/
TEST_F(ScheduleTest, parse)
{
  schedule = Schedule("data/increment.invalid.schedule");

  ASSERT_EQ(0, schedule.seed);
  ASSERT_EQ(3, schedule.programs.size());
  ASSERT_EQ(13, schedule.size());
}

/* parseFileNotFound **********************************************************/
TEST_F(ScheduleTest, parseFileNotFound)
{
  string file = "file_not_found";

  try
    {
      schedule = Schedule(file);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("file_not_found not found", e.what());
    }
}

/* parseIllegalSchedule *******************************************************/
TEST_F(ScheduleTest, parseIllegalSchedule)
{
  string dummyFile = "data/increment.asm";

  Parser<Schedule> parser(dummyFile);

  /* no seed */
  istringstream inbuf(" \
    0 = data/increment.checker.asm \
    1 = data/increment.asm \
    0 \
    1 \
    ");

  StreamRedirecter redirecter(parser.file, inbuf);

  redirecter.start();

  try
    {
      parser.parse(&schedule);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("'=' expected", e.what());
    }

  redirecter.stop();

  /* no program */
  schedule = Schedule();
  inbuf.str(" \
    seed = 0 \
    0 \
    1 \
    ");

  redirecter.start();

  try
    {
      parser.parse(&schedule);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("missing threads", e.what());
    }

  redirecter.stop();

  /* illegal seed (not an int) */
  schedule = Schedule();
  inbuf.str(" \
    0 = data/increment.asm \
    seed = wrong \
    0 \
    ");

  redirecter.start();

  try
    {
      parser.parse(&schedule);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("illegal seed [wrong]", e.what());
    }

  redirecter.stop();


  /* illegal thread id (unknown id) */
  schedule = Schedule();
  inbuf.str(" \
    1 = data/increment.asm \
    seed = 0 \
    0 \
    ");

  redirecter.start();

  try
    {
      parser.parse(&schedule);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("unknown thread id", e.what());
    }

  redirecter.stop();

  /* illegal thread id (not an int) */
  schedule = Schedule();
  inbuf.str(" \
    wrong = data/increment.asm \
    seed = 0 \
    0 \
    ");

  redirecter.start();

  try
    {
      parser.parse(&schedule);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("illegal thread id [wrong]", e.what());
    }

  /* illegal thread id (not an int) */
  schedule = Schedule();
  inbuf.str(" \
    1 = data/increment.asm \
    seed = 0 \
    wrong \
    ");

  redirecter.start();

  try
    {
      parser.parse(&schedule);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("illegal thread id [wrong]", e.what());
    }

  redirecter.stop();
}
