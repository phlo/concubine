#include <gtest/gtest.h>

#include "simulator.hh"

#include "program.hh"

namespace test {

//==============================================================================
// Thread tests
//==============================================================================

struct Thread : public ::testing::Test
{
  Program program;
  Simulator simulator = Simulator(std::make_shared<Program::List>(1));
  ::Thread thread = ::Thread(simulator, 0, program);
};

// Thread::load ================================================================

TEST_F(Thread, load)
{
  // direct
  simulator.heap[0] = 1;

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(1, thread.load(0));

  // indirect
  ASSERT_EQ(0, simulator.heap[1]);
  ASSERT_EQ(1, thread.load(1, true));

  // store buffer - direct
  thread.buffer.address = 1;
  thread.buffer.value = 1;
  thread.buffer.full = true;

  ASSERT_EQ(1, thread.load(1));

  // store buffer - indirect
  ASSERT_EQ(1, thread.load(0, true));
  ASSERT_EQ(1, thread.load(1, true));
}

// Thread::store ===============================================================

TEST_F(Thread, store)
{
  // store direct
  ASSERT_EQ(0, thread.buffer.address);
  ASSERT_EQ(0, thread.buffer.value);
  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(0, simulator.heap[0]);

  thread.store(0, 1, false);

  ASSERT_EQ(0, thread.buffer.address);
  ASSERT_EQ(1, thread.buffer.value);
  ASSERT_TRUE(thread.buffer.full);
  ASSERT_EQ(0, simulator.heap[0]);

  thread.state = ::Thread::State::flushing;
  thread.flush();

  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(1, simulator.heap[0]);

  // store indirect
  ASSERT_EQ(0, simulator.heap[1]);

  thread.store(0, 1, true);

  ASSERT_EQ(1, thread.buffer.address);
  ASSERT_EQ(1, thread.buffer.value);
  ASSERT_TRUE(thread.buffer.full);
  ASSERT_EQ(0, simulator.heap[1]);

  thread.state = ::Thread::State::flushing;
  thread.flush();

  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(1, simulator.heap[1]);
}

TEST_F(Thread, store_atomic)
{
  // store direct
  ASSERT_EQ(0, thread.buffer.address);
  ASSERT_EQ(0, thread.buffer.value);
  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(0, simulator.heap[0]);

  thread.store(0, 1, false, true);

  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(1, simulator.heap[0]);

  // store indirect
  ASSERT_EQ(0, simulator.heap[1]);

  thread.store(0, 1, true, true);

  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(1, simulator.heap[1]);
}

// Thread::flush ===============================================================

TEST_F(Thread, flush)
{
  thread.buffer.address = 0;
  thread.buffer.value = 1;
  thread.buffer.full = true;
  thread.state = ::Thread::State::flushing;

  ASSERT_EQ(0, simulator.heap[0]);

  thread.flush();

  ASSERT_EQ(1, simulator.heap[0]);
}

// Thread::execute =============================================================

TEST_F(Thread, execute)
{
  // success
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(::Thread::State::initial, thread.state);

  program.push_back(Instruction::create("ADDI", 1));

  thread.execute();

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);

  // fail - pc > program => STOPPED
  ASSERT_EQ(1, program.size());
  ASSERT_EQ(::Thread::State::halted, thread.state);

  try
    {
      thread.execute();
      ASSERT_TRUE(false) << "thread stopped: expected exception";
    }
  catch (...) {};

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
}

} // namespace test
