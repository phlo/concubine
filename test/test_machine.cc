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

/* activate_threads ***********************************************************/
TEST_F(MachineTest, activate_threads)
{
  Program program;

  ASSERT_TRUE(machine.active.empty());
  ASSERT_TRUE(machine.threads.empty());

  program.add(Instruction::Set::create("ADDI", 1));

  machine.create_thread(program);

  ASSERT_TRUE(machine.active.empty());
  ASSERT_EQ(1, machine.threads.size());
  ASSERT_EQ(Thread::State::INITIAL, machine.threads[0]->state);

  machine.activate_threads(machine.threads);

  ASSERT_EQ(1, machine.active.size());
  ASSERT_EQ(Thread::State::RUNNING, machine.active[0]->state);
  ASSERT_EQ(machine.threads[0], machine.active[0]);
}

/* create_thread **************************************************************/
TEST_F(MachineTest, create_thread)
{
  Program program;

  ASSERT_TRUE(machine.active.empty());
  ASSERT_TRUE(machine.threads.empty());
  ASSERT_TRUE(machine.threads_per_sync_id.empty());
  ASSERT_TRUE(machine.waiting_per_sync_id.empty());

  program.add(Instruction::Set::create("ADDI", 1));

  machine.create_thread(program);

  ASSERT_TRUE(machine.active.empty());
  ASSERT_EQ(1, machine.threads.size());
  ASSERT_TRUE(machine.threads_per_sync_id.empty());
  ASSERT_TRUE(machine.waiting_per_sync_id.empty());

  program.add(Instruction::Set::create("SYNC", 1));

  machine.create_thread(program);

  ASSERT_TRUE(machine.active.empty());
  ASSERT_EQ(2, machine.threads.size());
  ASSERT_EQ(1, machine.threads_per_sync_id[1].size());
  ASSERT_TRUE(machine.waiting_per_sync_id.empty());

  /* basically tests mapped default value */
  ASSERT_EQ(0, machine.waiting_per_sync_id[0]);
  ASSERT_TRUE(!machine.waiting_per_sync_id.empty());
}

/* run_simple *****************************************************************/
TEST_F(MachineTest, run_simple)
{
  cout.setstate(ios_base::failbit);

  Program program;

  program.add(Instruction::Set::create("ADDI", 1));

  machine.create_thread(program);
  machine.create_thread(program);

  ASSERT_EQ(0, machine.active.size());
  ASSERT_EQ(2, machine.threads.size());
  ASSERT_TRUE(machine.threads_per_sync_id.empty());
  ASSERT_TRUE(machine.waiting_per_sync_id.empty());

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

/* run_add_sync_exit **********************************************************/
TEST_F(MachineTest, run_add_sync_exit)
{
  cout.setstate(ios_base::failbit);

  Program program;

  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("SYNC", 1));
  program.add(Instruction::Set::create("EXIT", 1));

  machine.create_thread(program);
  machine.create_thread(program);

  ASSERT_EQ(0, machine.active.size());
  ASSERT_EQ(2, machine.threads.size());
  ASSERT_EQ(2, machine.threads_per_sync_id[1].size());
  ASSERT_EQ(0, machine.waiting_per_sync_id[1]);

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
              EXPECT_EQ(1, machine.waiting_per_sync_id[1]);

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
              EXPECT_EQ(0, machine.waiting_per_sync_id[1]);

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

/* run_race_condition *********************************************************/
TEST_F(MachineTest, run_race_condition)
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

  machine.create_thread(checker);
  machine.create_thread(program);
  machine.create_thread(program);

  ASSERT_EQ(0, machine.active.size());
  ASSERT_EQ(3, machine.threads.size());
  ASSERT_EQ(3, machine.threads_per_sync_id[1].size());
  ASSERT_EQ(0, machine.waiting_per_sync_id[1]);

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
              EXPECT_EQ(1, machine.waiting_per_sync_id[1]);
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
              EXPECT_EQ(1, machine.waiting_per_sync_id[1]);
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
              EXPECT_EQ(0, machine.waiting_per_sync_id[1]);
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

/* run_zero_bound *************************************************************/
TEST_F(MachineTest, run_zero_bound)
{
  cout.setstate(ios_base::failbit);

  Program program;

  program.add(Instruction::Set::create("JMP", 0));

  machine.create_thread(program);

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

/* simulate_increment_sync ****************************************************/
TEST_F(MachineTest, simulate_increment_sync)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.sync.t2.k16.schedule");
  string schedule(( istreambuf_iterator<char>(schedule_file) ),
                    istreambuf_iterator<char>());

  Program increment_0("data/increment.sync.thread.0.asm");
  Program increment_n("data/increment.sync.thread.n.asm");

  machine.seed  = 0;
  machine.bound = 16;

  machine.create_thread(increment_0);
  machine.create_thread(increment_n);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* run it */
  ASSERT_EQ(0, machine.simulate());

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(schedule, ss.str());
}

/* simulate_increment_cas *****************************************************/
TEST_F(MachineTest, simulate_increment_cas)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.cas.t2.k16.schedule");
  string schedule(( istreambuf_iterator<char>(schedule_file) ),
                    istreambuf_iterator<char>());

  Program increment("data/increment.cas.asm");

  machine.seed  = 0;
  machine.bound = 16;

  machine.create_thread(increment);
  machine.create_thread(increment);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* run it */
  ASSERT_EQ(0, machine.simulate());

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(schedule, ss.str());
}

/* replay_increment_sync ******************************************************/
TEST_F(MachineTest, replay_increment_sync)
{
  string schedule_file = "data/increment.sync.t2.k16.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string schedule_str((istreambuf_iterator<char>(sfs)),
                      istreambuf_iterator<char>());

  Schedule schedule(schedule_file);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* replay */
  ASSERT_EQ(0, machine.replay(schedule));

  ASSERT_EQ(2, machine.memory[0]);

  ASSERT_EQ(1, machine.threads[0]->accu);
  ASSERT_EQ(0, machine.threads[0]->mem);
  ASSERT_EQ(2, machine.threads[1]->accu);
  ASSERT_EQ(0, machine.threads[1]->mem);

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(schedule_str, ss.str());
}

/* replay_increment_cas *******************************************************/
TEST_F(MachineTest, replay_increment_cas)
{
  string schedule_file = "data/increment.cas.t2.k16.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string schedule_str((istreambuf_iterator<char>(sfs)),
                      istreambuf_iterator<char>());

  Schedule schedule(schedule_file);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* replay */
  ASSERT_EQ(0, machine.replay(schedule));

  ASSERT_EQ(2, machine.memory[0]);

  ASSERT_EQ(1, machine.threads[0]->accu);
  ASSERT_EQ(1, machine.threads[0]->mem);
  ASSERT_EQ(0, machine.threads[1]->accu);
  ASSERT_EQ(0, machine.threads[1]->mem);

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(schedule_str, ss.str());
}
