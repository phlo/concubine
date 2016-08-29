#include <gtest/gtest.h>

#include <fstream>
#include <sstream>
#include <streambuf>
#include <functional>

#include "machine.hh"

#include "program.hh"
#include "schedule.hh"
#include "streamredirecter.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct MachineTest : public ::testing::Test
{
  Machine machine;
};

/* activateThreads ************************************************************/
TEST_F(MachineTest, activateThreads)
{
  Program program;

  ASSERT_TRUE(machine.active.empty());
  ASSERT_TRUE(machine.threads.empty());

  program.add(Instruction::Set::create("ADDI", 1));

  machine.createThread(program);

  ASSERT_TRUE(machine.active.empty());
  ASSERT_EQ(1, machine.threads.size());
  ASSERT_EQ(Thread::State::INITIAL, machine.threads[0]->state);

  machine.activateThreads(machine.threads);

  ASSERT_EQ(1, machine.active.size());
  ASSERT_EQ(Thread::State::RUNNING, machine.active[0]->state);
  ASSERT_EQ(machine.threads[0], machine.active[0]);
}

/* createThread ***************************************************************/
TEST_F(MachineTest, createThread)
{
  Program program;

  ASSERT_TRUE(machine.active.empty());
  ASSERT_TRUE(machine.threads.empty());
  ASSERT_TRUE(machine.threadsPerSyncID.empty());
  ASSERT_TRUE(machine.waitingPerSyncID.empty());

  program.add(Instruction::Set::create("ADDI", 1));

  machine.createThread(program);

  ASSERT_TRUE(machine.active.empty());
  ASSERT_EQ(1, machine.threads.size());
  ASSERT_TRUE(machine.threadsPerSyncID.empty());
  ASSERT_TRUE(machine.waitingPerSyncID.empty());

  program.add(Instruction::Set::create("SYNC", 1));

  machine.createThread(program);

  ASSERT_TRUE(machine.active.empty());
  ASSERT_EQ(2, machine.threads.size());
  ASSERT_EQ(1, machine.threadsPerSyncID[1].size());
  ASSERT_TRUE(machine.waitingPerSyncID.empty());

  /* basically tests mapped default value */
  ASSERT_EQ(0, machine.waitingPerSyncID[0]);
  ASSERT_TRUE(!machine.waitingPerSyncID.empty());
}

/* runSimple ******************************************************************/
TEST_F(MachineTest, runSimple)
{
  cout.setstate(ios_base::failbit);

  Program program;

  program.add(Instruction::Set::create("ADDI", 1));

  machine.createThread(program);
  machine.createThread(program);

  ASSERT_EQ(0, machine.active.size());
  ASSERT_EQ(2, machine.threads.size());
  ASSERT_TRUE(machine.threadsPerSyncID.empty());
  ASSERT_TRUE(machine.waitingPerSyncID.empty());

  unsigned long step = 0;

  /* NOTE: EXPECT_* required by lambda function */
  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial -> t0: pre ADDI 1 */
            {
              return machine.threads[0];
            }
        case 1: /* t0: post ADDI 1 && next == t1 */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(1, machine.threads[0]->accu);
              EXPECT_EQ(0, machine.threads[1]->pc);
              EXPECT_EQ(0, machine.threads[1]->accu);

              return machine.threads[1];
            }
        case 2: /* t1: post ADDI 1 && next == t0 */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(1, machine.threads[0]->accu);
              EXPECT_EQ(1, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);

              EXPECT_EQ(Thread::State::STOPPED, machine.threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, machine.threads[1]->state);

              return machine.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  /* run it */
  ASSERT_EQ(0, machine.run(scheduler));

  EXPECT_EQ(Thread::State::STOPPED, machine.threads[0]->state);
  EXPECT_EQ(Thread::State::STOPPED, machine.threads[1]->state);

  cout.clear();
}

/* runAddSyncExit *************************************************************/
TEST_F(MachineTest, runAddSyncExit)
{
  cout.setstate(ios_base::failbit);

  Program program;

  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("SYNC", 1));
  program.add(Instruction::Set::create("EXIT", 1));

  machine.createThread(program);
  machine.createThread(program);

  ASSERT_EQ(0, machine.active.size());
  ASSERT_EQ(2, machine.threads.size());
  ASSERT_EQ(2, machine.threadsPerSyncID[1].size());
  ASSERT_EQ(0, machine.waitingPerSyncID[1]);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial -> t0: pre ADDI 1 */
            {
              return machine.threads[0];
            }
        case 1: /* t0: post ADDI 1 && next == t1 */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(1, machine.threads[0]->accu);
              EXPECT_EQ(0, machine.threads[1]->pc);
              EXPECT_EQ(0, machine.threads[1]->accu);

              return machine.threads[1];
            }
        case 2: /* t1: post ADDI 1 && next == t0 */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(1, machine.threads[0]->accu);
              EXPECT_EQ(1, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);

              return machine.threads[0];
            }
        case 3: /* t0: post SYNC 1 && next == t1 */
            {
              EXPECT_EQ(2, machine.threads[0]->pc);
              EXPECT_EQ(1, machine.threads[0]->accu);
              EXPECT_EQ(1, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);

              EXPECT_EQ(Thread::State::WAITING, machine.threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, machine.threads[1]->state);

              EXPECT_EQ(1, machine.active.size());
              EXPECT_EQ(1, machine.waitingPerSyncID[1]);

              return machine.threads[1];
            }
        case 4: /* t1: post SYNC 1 (both active again) && next == t0 */
            {
              EXPECT_EQ(2, machine.threads[0]->pc);
              EXPECT_EQ(1, machine.threads[0]->accu);
              EXPECT_EQ(2, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);

              EXPECT_EQ(Thread::State::RUNNING, machine.threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, machine.threads[1]->state);

              EXPECT_EQ(2, machine.active.size());
              EXPECT_EQ(0, machine.waitingPerSyncID[1]);

              return machine.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  /* run it */
  ASSERT_EQ(1, machine.run(scheduler));

  cout.clear();
}

/* runRaceCondition ***********************************************************/
TEST_F(MachineTest, runRaceCondition)
{
  cout.setstate(ios_base::failbit);

  Program program;

  program.add(Instruction::Set::create("LOAD", 1));
  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("STORE", 1));
  program.add(Instruction::Set::create("SYNC", 1));

  Program checker;

  checker.add(Instruction::Set::create("SYNC", 1));
  checker.add(Instruction::Set::create("LOAD", 1));
  checker.add(Instruction::Set::create("SUBI", 2));
  checker.add(Instruction::Set::create("JZ", 5));
  checker.add(Instruction::Set::create("EXIT", 1));
  checker.add(Instruction::Set::create("EXIT", 0));

  machine.createThread(checker);
  machine.createThread(program);
  machine.createThread(program);

  ASSERT_EQ(0, machine.active.size());
  ASSERT_EQ(3, machine.threads.size());
  ASSERT_EQ(3, machine.threadsPerSyncID[1].size());
  ASSERT_EQ(0, machine.waitingPerSyncID[1]);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial = t0 [SYNC 1] */
            {
              EXPECT_EQ(0, machine.memory[1]);

              EXPECT_EQ(0, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(0, machine.threads[1]->pc);
              EXPECT_EQ(0, machine.threads[1]->accu);
              EXPECT_EQ(0, machine.threads[2]->pc);
              EXPECT_EQ(0, machine.threads[2]->accu);

              EXPECT_EQ(3, machine.active.size());

              return machine.threads[0];
            }
        case 1: /* prev = t0 [SYNC 1] | next = t1 [LOAD 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(0, machine.threads[1]->pc);
              EXPECT_EQ(0, machine.threads[1]->accu);
              EXPECT_EQ(0, machine.threads[2]->pc);
              EXPECT_EQ(0, machine.threads[2]->accu);

              EXPECT_EQ(2, machine.active.size());
              EXPECT_EQ(1, machine.waitingPerSyncID[1]);
              EXPECT_EQ(Thread::State::WAITING, machine.threads[0]->state);

              return machine.threads[1];
            }
        case 2: /* prev = t1 [LOAD 1] | next = t2 [LOAD 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(1, machine.threads[1]->pc);
              EXPECT_EQ(0, machine.threads[1]->accu);
              EXPECT_EQ(0, machine.threads[2]->pc);
              EXPECT_EQ(0, machine.threads[2]->accu);

              return machine.threads[2];
            }
        case 3: /* prev = t2 [LOAD 1] | next = t1 [ADDI 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(1, machine.threads[1]->pc);
              EXPECT_EQ(0, machine.threads[1]->accu);
              EXPECT_EQ(1, machine.threads[2]->pc);
              EXPECT_EQ(0, machine.threads[2]->accu);

              return machine.threads[1];
            }
        case 4: /* prev = t1 [ADDI 1] | next = t2 [ADDI 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(2, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(1, machine.threads[2]->pc);
              EXPECT_EQ(0, machine.threads[2]->accu);

              return machine.threads[2];
            }
        case 5: /* prev = t2 [ADDI 1] | next = t1 [STORE 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(2, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(2, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              return machine.threads[1];
            }
        case 6: /* prev = t1 [STORE 1] | next = t2 [STORE 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(3, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(2, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              EXPECT_EQ(1, machine.memory[1]);

              return machine.threads[2];
            }
        case 7: /* prev = t2 [STORE 1] | next = t1 [SYNC 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(3, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(3, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              EXPECT_EQ(1, machine.memory[1]);

              return machine.threads[1];
            }
        case 8: /* prev = t1 [SYNC 1] | next = t2 [SYNC 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(4, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(3, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              EXPECT_EQ(1, machine.active.size());
              EXPECT_EQ(1, machine.waitingPerSyncID[1]);
              EXPECT_EQ(Thread::State::WAITING, machine.threads[0]->state);
              EXPECT_EQ(Thread::State::STOPPED, machine.threads[1]->state);

              return machine.threads[2];
            }
        case 9: /* prev = t2 [SYNC 1] | next = t0 [LOAD 1] */
            {
              EXPECT_EQ(1, machine.threads[0]->pc);
              EXPECT_EQ(0, machine.threads[0]->accu);
              EXPECT_EQ(4, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(4, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              EXPECT_EQ(1, machine.active.size());
              EXPECT_EQ(0, machine.waitingPerSyncID[1]);
              EXPECT_EQ(Thread::State::RUNNING, machine.threads[0]->state);
              EXPECT_EQ(Thread::State::STOPPED, machine.threads[1]->state);
              EXPECT_EQ(Thread::State::STOPPED, machine.threads[2]->state);

              return machine.threads[0];
            }
        case 10: /* prev = t0 [LOAD 1] | next = t0 [SUBI 2] */
            {
              EXPECT_EQ(2, machine.threads[0]->pc);
              EXPECT_EQ(1, machine.threads[0]->accu);
              EXPECT_EQ(4, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(4, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              return machine.threads[0];
            }
        case 11: /* prev = t0 [SUBI 2] | next = t0 [JZ 5] */
            {
              EXPECT_EQ(3, machine.threads[0]->pc);
              EXPECT_EQ(word(-1), machine.threads[0]->accu);
              EXPECT_EQ(4, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(4, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              return machine.threads[0];
            }
        case 12: /* prev = t0 [JZ 5] | next = t0 [EXIT 1] */
            {
              EXPECT_EQ(4, machine.threads[0]->pc);
              EXPECT_EQ(word(-1), machine.threads[0]->accu);
              EXPECT_EQ(4, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(4, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              return machine.threads[0];
            }
        case 13: /* last = t0 [EXIT 1] */
            {
              EXPECT_EQ(4, machine.threads[0]->pc);
              EXPECT_EQ(word(-1), machine.threads[0]->accu);
              EXPECT_EQ(4, machine.threads[1]->pc);
              EXPECT_EQ(1, machine.threads[1]->accu);
              EXPECT_EQ(4, machine.threads[2]->pc);
              EXPECT_EQ(1, machine.threads[2]->accu);

              EXPECT_EQ(Thread::State::EXITING, machine.threads[0]->state);

              return machine.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  /* run it */
  ASSERT_EQ(1, machine.run(scheduler));

  cout.clear();
}

/* runZeroBound ***************************************************************/
TEST_F(MachineTest, runZeroBound)
{
  cout.setstate(ios_base::failbit);

  Program program;

  program.add(Instruction::Set::create("JMP", 0));

  machine.createThread(program);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0:
            {
              return machine.threads[0];
            }
        case 1:
            {
              EXPECT_EQ(0, machine.threads[0]->pc);

              return machine.threads[0];
            }
        case 2:
            {
              /* 3 iterations are enough ... */
              machine.bound = 1;

              EXPECT_EQ(0, machine.threads[0]->pc);

              return machine.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  /* run it */
  ASSERT_EQ(0, machine.run(scheduler));

  cout.clear();
}

/* simulateIncrement0 *********************************************************/
TEST_F(MachineTest, simulateIncrement0)
{
  /* read expected schedule from file */
  ifstream scheduleFile("data/increment.invalid.schedule");
  string schedule(( istreambuf_iterator<char>(scheduleFile) ),
                    istreambuf_iterator<char>());

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  machine.seed          = 0;

  string checkerFile    = "data/increment.checker.asm";
  string incrementFile  = "data/increment.asm";

  Program checker(checkerFile);
  Program increment_1(incrementFile);
  Program increment_2(incrementFile);

  machine.createThread(checker);
  machine.createThread(increment_1);
  machine.createThread(increment_2);

  /* redirect stdout */
  redirecter.start();

  /* run it */
  ASSERT_EQ(1, machine.simulate());

  redirecter.stop();

  /* compare output */
  ASSERT_STREQ(schedule.c_str(), ss.str().c_str());
}

/* simulateIncrementCAS *******************************************************/
TEST_F(MachineTest, simulateIncrementCAS)
{
  /* read expected schedule from file */
  ifstream scheduleFile("data/increment.cas.schedule");
  string schedule(( istreambuf_iterator<char>(scheduleFile) ),
                    istreambuf_iterator<char>());

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  machine.seed          = 0;

  string checkerFile    = "data/increment.checker.asm";
  string incrementFile  = "data/increment.cas.asm";

  Program checker(checkerFile);
  Program increment_1(incrementFile);
  Program increment_2(incrementFile);

  machine.createThread(checker);
  machine.createThread(increment_1);
  machine.createThread(increment_2);

  /* redirect stdout */
  redirecter.start();

  /* run it */
  ASSERT_EQ(0, machine.simulate());

  redirecter.stop();

  /* compare output */
  ASSERT_STREQ(schedule.c_str(), ss.str().c_str());
}

/* replayIncrementCAS *********************************************************/
TEST_F(MachineTest, replayIncrement0)
{
  string scheduleFile   = "data/increment.invalid.schedule";

  /* read expected schedule from file */
  ifstream sfs(scheduleFile);
  string scheduleStr((istreambuf_iterator<char>(sfs)),
                      istreambuf_iterator<char>());

  Schedule schedule(scheduleFile);

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* replay */
  ASSERT_EQ(1, machine.replay(schedule));

  redirecter.stop();

  /* compare output */
  ASSERT_STREQ(scheduleStr.c_str(), ss.str().c_str());
}

/* replayIncrementCAS *********************************************************/
TEST_F(MachineTest, replayIncrementCAS)
{
  string scheduleFile   = "data/increment.cas.schedule";

  /* read expected schedule from file */
  ifstream sfs(scheduleFile);
  string scheduleStr((istreambuf_iterator<char>(sfs)),
                      istreambuf_iterator<char>());

  Schedule schedule(scheduleFile);

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* replay */
  ASSERT_EQ(0, machine.replay(schedule));

  redirecter.stop();

  /* compare output */
  ASSERT_STREQ(scheduleStr.c_str(), ss.str().c_str());
}
