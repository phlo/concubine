#include <gtest/gtest.h>

#include "program.hh"
#include "simulator.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ThreadTest : public ::testing::Test
{
  Program         program;
  Simulator       simulator;
  Thread          thread = Thread(simulator, 0, program);
};

/* Load ***********************************************************************/
TEST_F(ThreadTest, load)
{
  /* load direct */
  simulator.heap[0] = 1;

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(1, thread.load(0, false));

  /* load indirect */
  ASSERT_EQ(0, simulator.heap[1]);
  ASSERT_EQ(1, thread.load(1, true));
}

/* Store **********************************************************************/
TEST_F(ThreadTest, store)
{
  /* store direct */
  ASSERT_EQ(0, simulator.heap[0]);

  thread.store(0, 1, false);

  ASSERT_EQ(1, simulator.heap[0]);

  /* store indirect */
  ASSERT_EQ(0, simulator.heap[1]);

  thread.store(1, 0, true);

  ASSERT_EQ(0, simulator.heap[0]);
}

/* Execute ********************************************************************/
TEST_F(ThreadTest, execute)
{
  cout.setstate(ios_base::failbit);

  /* success */
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(Thread::State::INITIAL, thread.state);

  program.push_back(Instruction::Set::create("ADDI", 1));

  thread.execute();

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);

  /* fail - pc > program => STOPPED */
  ASSERT_EQ(1, program.size());
  ASSERT_EQ(Thread::State::STOPPED, thread.state);

  try
    {
      thread.execute();
      ASSERT_TRUE(false) << "thread stopped: expected exception";
    }
  catch (...) {};

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);

  cout.clear();
}
