#include <gtest/gtest.h>

#include "machine.hh"
#include "program.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ThreadTest : public ::testing::Test
{
  Program         program;
  Thread          thread;
  Machine         machine;

  ThreadTest () : thread(machine, 0, program) {};
};

/* Load ***********************************************************************/
TEST_F(ThreadTest, load)
{
  /* load direct */
  machine.memory[0] = 1;

  ASSERT_EQ(1, machine.memory[0]);
  ASSERT_EQ(1, thread.load(0, false));

  /* load indirect */
  ASSERT_EQ(0, machine.memory[1]);
  ASSERT_EQ(1, thread.load(1, true));
}

/* Store **********************************************************************/
TEST_F(ThreadTest, store)
{
  /* store direct */
  ASSERT_EQ(0, machine.memory[0]);

  thread.store(0, 1, false);

  ASSERT_EQ(1, machine.memory[0]);

  /* store indirect */
  ASSERT_EQ(0, machine.memory[1]);

  thread.store(1, 0, true);

  ASSERT_EQ(0, machine.memory[0]);
}

/* Execute ********************************************************************/
TEST_F(ThreadTest, execute)
{
  cout.setstate(ios_base::failbit);

  /* success */
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(Thread::State::INITIAL, thread.state);

  program.add(Instruction::Set::create("ADDI", 1));

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
