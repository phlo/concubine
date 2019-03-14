#include <gtest/gtest.h>

#include <fstream>
#include <sstream>
#include <streambuf>
#include <functional>

#include "simulator.hh"

#include "parser.hh"
#include "streamredirecter.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct SimulatorTest : public ::testing::Test
{
  Program     program;
  SchedulePtr schedule;
  Simulator   simulator;
};

/* activate_threads ***********************************************************/
TEST_F(SimulatorTest, activate_threads)
{
  ASSERT_TRUE(simulator.active.empty());
  ASSERT_TRUE(simulator.threads.empty());

  program.add(Instruction::Set::create("ADDI", 1));

  simulator.create_thread(program);

  ASSERT_TRUE(simulator.active.empty());
  ASSERT_EQ(1, simulator.threads.size());
  ASSERT_EQ(Thread::State::INITIAL, simulator.threads[0]->state);

  simulator.activate_threads(simulator.threads);

  ASSERT_EQ(1, simulator.active.size());
  ASSERT_EQ(Thread::State::RUNNING, simulator.active[0]->state);
  ASSERT_EQ(simulator.threads[0], simulator.active[0]);
}

/* create_thread **************************************************************/
TEST_F(SimulatorTest, create_thread)
{
  ASSERT_TRUE(simulator.active.empty());
  ASSERT_TRUE(simulator.threads.empty());
  ASSERT_TRUE(simulator.threads_per_sync_id.empty());
  ASSERT_TRUE(simulator.waiting_per_sync_id.empty());

  program.add(Instruction::Set::create("ADDI", 1));

  simulator.create_thread(program);

  ASSERT_EQ(0, simulator.threads.back()->id);
  ASSERT_TRUE(simulator.active.empty());
  ASSERT_EQ(1, simulator.threads.size());
  ASSERT_TRUE(simulator.threads_per_sync_id.empty());
  ASSERT_TRUE(simulator.waiting_per_sync_id.empty());

  program.add(Instruction::Set::create("SYNC", 1));

  simulator.create_thread(program);

  ASSERT_EQ(1, simulator.threads.back()->id);
  ASSERT_TRUE(simulator.active.empty());
  ASSERT_EQ(2, simulator.threads.size());
  ASSERT_EQ(1, simulator.threads_per_sync_id[1].size());
  ASSERT_TRUE(simulator.waiting_per_sync_id.empty());

  /* basically tests mapped default value */
  ASSERT_EQ(0, simulator.waiting_per_sync_id[0]);
  ASSERT_TRUE(!simulator.waiting_per_sync_id.empty());
}

/* run_simple *****************************************************************/
TEST_F(SimulatorTest, run_simple)
{
  cout.setstate(ios_base::failbit);

  program.add(Instruction::Set::create("ADDI", 1));

  simulator.create_thread(program);
  simulator.create_thread(program);

  ASSERT_EQ(0, simulator.active.size());
  ASSERT_EQ(2, simulator.threads.size());
  ASSERT_TRUE(simulator.threads_per_sync_id.empty());
  ASSERT_TRUE(simulator.waiting_per_sync_id.empty());

  unsigned long step = 0;

  /* NOTE: EXPECT_* required by lambda function */
  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial -> t0: pre ADDI 1 */
            {
              return simulator.threads[0];
            }
        case 1: /* t0: post ADDI 1 && next == t1 */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(1, simulator.threads[0]->accu);
              EXPECT_EQ(0, simulator.threads[1]->pc);
              EXPECT_EQ(0, simulator.threads[1]->accu);

              return simulator.threads[1];
            }
        case 2: /* t1: post ADDI 1 && next == t0 */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(1, simulator.threads[0]->accu);
              EXPECT_EQ(1, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);

              EXPECT_EQ(Thread::State::STOPPED, simulator.threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, simulator.threads[1]->state);

              return simulator.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator.run(scheduler);

  EXPECT_EQ(2, step);

  EXPECT_EQ(Thread::State::STOPPED, simulator.threads[0]->state);
  EXPECT_EQ(Thread::State::STOPPED, simulator.threads[1]->state);

  /* check Schedule */
  ASSERT_EQ(0, schedule->exit);

  unordered_map<word, vector<word>> pcs({{0, {1, 1}}, {1, {0, 1}}});
  ASSERT_EQ(pcs, schedule->pcs);

  unordered_map<word, vector<word>> accus({{0, {1, 1}}, {1, {0, 1}}});
  ASSERT_EQ(accus, schedule->accus);

  unordered_map<word, vector<word>> mems({{0, {0, 0}}, {1, {0, 0}}});
  ASSERT_EQ(mems, schedule->mems);

  vector<unordered_map<word, word>> heap({{}, {}});
  ASSERT_EQ(heap, schedule->heaps);

  cout.clear();
}

/* run_add_sync_exit **********************************************************/
TEST_F(SimulatorTest, run_add_sync_exit)
{
  cout.setstate(ios_base::failbit);

  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("SYNC", 1));
  program.add(Instruction::Set::create("EXIT", 1));

  simulator.create_thread(program);
  simulator.create_thread(program);

  ASSERT_EQ(0, simulator.active.size());
  ASSERT_EQ(2, simulator.threads.size());
  ASSERT_EQ(2, simulator.threads_per_sync_id[1].size());
  ASSERT_EQ(0, simulator.waiting_per_sync_id[1]);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial -> t0: pre ADDI 1 */
            {
              return simulator.threads[0];
            }
        case 1: /* t0: post ADDI 1 && next == t1 */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(1, simulator.threads[0]->accu);
              EXPECT_EQ(0, simulator.threads[1]->pc);
              EXPECT_EQ(0, simulator.threads[1]->accu);

              return simulator.threads[1];
            }
        case 2: /* t1: post ADDI 1 && next == t0 */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(1, simulator.threads[0]->accu);
              EXPECT_EQ(1, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);

              return simulator.threads[0];
            }
        case 3: /* t0: post SYNC 1 && next == t1 */
            {
              EXPECT_EQ(2, simulator.threads[0]->pc);
              EXPECT_EQ(1, simulator.threads[0]->accu);
              EXPECT_EQ(1, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);

              EXPECT_EQ(Thread::State::WAITING, simulator.threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, simulator.threads[1]->state);

              EXPECT_EQ(1, simulator.active.size());
              EXPECT_EQ(1, simulator.waiting_per_sync_id[1]);

              return simulator.threads[1];
            }
        case 4: /* t1: post SYNC 1 (both active again) && next == t0 */
            {
              EXPECT_EQ(2, simulator.threads[0]->pc);
              EXPECT_EQ(1, simulator.threads[0]->accu);
              EXPECT_EQ(2, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);

              EXPECT_EQ(Thread::State::RUNNING, simulator.threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, simulator.threads[1]->state);

              EXPECT_EQ(2, simulator.active.size());
              EXPECT_EQ(0, simulator.waiting_per_sync_id[1]);

              return simulator.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator.run(scheduler);

  EXPECT_EQ(step, 5);

  EXPECT_EQ(Thread::State::EXITING, simulator.threads[0]->state);
  EXPECT_EQ(Thread::State::RUNNING, simulator.threads[1]->state);

  /* check Schedule */
  ASSERT_EQ(1, schedule->exit);

  unordered_map<word, vector<word>> pcs({
    {0, {1, 1, 2, 2, 2}},
    {1, {0, 1, 1, 2, 2}}});
  ASSERT_EQ(pcs, schedule->pcs);

  unordered_map<word, vector<word>> accus({
    {0, {1, 1, 1, 1, 1}},
    {1, {0, 1, 1, 1, 1}}});
  ASSERT_EQ(accus, schedule->accus);

  unordered_map<word, vector<word>> mems({
    {0, {0, 0, 0, 0, 0}},
    {1, {0, 0, 0, 0, 0}}});
  ASSERT_EQ(mems, schedule->mems);

  vector<unordered_map<word, word>> heap({{}, {}, {}, {}, {}});
  ASSERT_EQ(heap, schedule->heaps);

  cout.clear();
}

/* run_race_condition *********************************************************/
TEST_F(SimulatorTest, run_race_condition)
{
  cout.setstate(ios_base::failbit);

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

  simulator.create_thread(checker);
  simulator.create_thread(program);
  simulator.create_thread(program);

  ASSERT_EQ(0, simulator.active.size());
  ASSERT_EQ(3, simulator.threads.size());
  ASSERT_EQ(3, simulator.threads_per_sync_id[1].size());
  ASSERT_EQ(0, simulator.waiting_per_sync_id[1]);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial = t0 [SYNC 1] */
            {
              EXPECT_EQ(0, simulator.heap[1]);

              EXPECT_EQ(0, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(0, simulator.threads[1]->pc);
              EXPECT_EQ(0, simulator.threads[1]->accu);
              EXPECT_EQ(0, simulator.threads[2]->pc);
              EXPECT_EQ(0, simulator.threads[2]->accu);

              EXPECT_EQ(3, simulator.active.size());

              return simulator.threads[0];
            }
        case 1: /* prev = t0 [SYNC 1] | next = t1 [LOAD 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(0, simulator.threads[1]->pc);
              EXPECT_EQ(0, simulator.threads[1]->accu);
              EXPECT_EQ(0, simulator.threads[2]->pc);
              EXPECT_EQ(0, simulator.threads[2]->accu);

              EXPECT_EQ(2, simulator.active.size());
              EXPECT_EQ(1, simulator.waiting_per_sync_id[1]);
              EXPECT_EQ(Thread::State::WAITING, simulator.threads[0]->state);

              return simulator.threads[1];
            }
        case 2: /* prev = t1 [LOAD 1] | next = t2 [LOAD 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(1, simulator.threads[1]->pc);
              EXPECT_EQ(0, simulator.threads[1]->accu);
              EXPECT_EQ(0, simulator.threads[2]->pc);
              EXPECT_EQ(0, simulator.threads[2]->accu);

              return simulator.threads[2];
            }
        case 3: /* prev = t2 [LOAD 1] | next = t1 [ADDI 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(1, simulator.threads[1]->pc);
              EXPECT_EQ(0, simulator.threads[1]->accu);
              EXPECT_EQ(1, simulator.threads[2]->pc);
              EXPECT_EQ(0, simulator.threads[2]->accu);

              return simulator.threads[1];
            }
        case 4: /* prev = t1 [ADDI 1] | next = t2 [ADDI 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(2, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(1, simulator.threads[2]->pc);
              EXPECT_EQ(0, simulator.threads[2]->accu);

              return simulator.threads[2];
            }
        case 5: /* prev = t2 [ADDI 1] | next = t1 [STORE 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(2, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(2, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              return simulator.threads[1];
            }
        case 6: /* prev = t1 [STORE 1] | next = t2 [STORE 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(3, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(2, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              EXPECT_EQ(1, simulator.heap[1]);

              return simulator.threads[2];
            }
        case 7: /* prev = t2 [STORE 1] | next = t1 [SYNC 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(3, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(3, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              EXPECT_EQ(1, simulator.heap[1]);

              return simulator.threads[1];
            }
        case 8: /* prev = t1 [SYNC 1] | next = t2 [SYNC 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(4, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(3, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              EXPECT_EQ(1, simulator.active.size());
              EXPECT_EQ(1, simulator.waiting_per_sync_id[1]);
              EXPECT_EQ(Thread::State::WAITING, simulator.threads[0]->state);
              EXPECT_EQ(Thread::State::STOPPED, simulator.threads[1]->state);

              return simulator.threads[2];
            }
        case 9: /* prev = t2 [SYNC 1] | next = t0 [LOAD 1] */
            {
              EXPECT_EQ(1, simulator.threads[0]->pc);
              EXPECT_EQ(0, simulator.threads[0]->accu);
              EXPECT_EQ(4, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(4, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              EXPECT_EQ(1, simulator.active.size());
              EXPECT_EQ(0, simulator.waiting_per_sync_id[1]);
              EXPECT_EQ(Thread::State::RUNNING, simulator.threads[0]->state);
              EXPECT_EQ(Thread::State::STOPPED, simulator.threads[1]->state);
              EXPECT_EQ(Thread::State::STOPPED, simulator.threads[2]->state);

              return simulator.threads[0];
            }
        case 10: /* prev = t0 [LOAD 1] | next = t0 [SUBI 2] */
            {
              EXPECT_EQ(2, simulator.threads[0]->pc);
              EXPECT_EQ(1, simulator.threads[0]->accu);
              EXPECT_EQ(4, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(4, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              return simulator.threads[0];
            }
        case 11: /* prev = t0 [SUBI 2] | next = t0 [JZ 5] */
            {
              EXPECT_EQ(3, simulator.threads[0]->pc);
              EXPECT_EQ(word(-1), simulator.threads[0]->accu);
              EXPECT_EQ(4, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(4, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              return simulator.threads[0];
            }
        case 12: /* prev = t0 [JZ 5] | next = t0 [EXIT 1] */
            {
              EXPECT_EQ(4, simulator.threads[0]->pc);
              EXPECT_EQ(word(-1), simulator.threads[0]->accu);
              EXPECT_EQ(4, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(4, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              return simulator.threads[0];
            }
        case 13: /* last = t0 [EXIT 1] */
            {
              EXPECT_EQ(4, simulator.threads[0]->pc);
              EXPECT_EQ(word(-1), simulator.threads[0]->accu);
              EXPECT_EQ(4, simulator.threads[1]->pc);
              EXPECT_EQ(1, simulator.threads[1]->accu);
              EXPECT_EQ(4, simulator.threads[2]->pc);
              EXPECT_EQ(1, simulator.threads[2]->accu);

              EXPECT_EQ(Thread::State::EXITING, simulator.threads[0]->state);

              return simulator.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator.run(scheduler);

  EXPECT_EQ(13, step);

  EXPECT_EQ(Thread::State::EXITING, simulator.threads[0]->state);
  EXPECT_EQ(Thread::State::STOPPED, simulator.threads[1]->state);
  EXPECT_EQ(Thread::State::STOPPED, simulator.threads[2]->state);

  /* check Schedule */
  ASSERT_EQ(1, schedule->exit);

  unordered_map<word, vector<word>> pcs({
    {0, {1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4}},
    {1, {0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 4, 4, 4}},
    {2, {0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 4, 4}}});
  ASSERT_EQ(pcs, schedule->pcs);

  unordered_map<word, vector<word>> accus({
    {0, {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 65535, 65535, 1}},
    {1, {0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}},
    {2, {0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1}}});
  ASSERT_EQ(accus, schedule->accus);

  unordered_map<word, vector<word>> mems({
    {0, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
    {1, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}},
    {2, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}}});
  ASSERT_EQ(mems, schedule->mems);

  vector<unordered_map<word, word>> heap({
    {{1, 0}},
    {{1, 0}},
    {{1, 0}},
    {{1, 0}},
    {{1, 0}},
    {{1, 1}},
    {{1, 1}},
    {{1, 1}},
    {{1, 1}},
    {{1, 1}},
    {{1, 1}},
    {{1, 1}},
    {{1, 1}}});
  ASSERT_EQ(heap, schedule->heaps);

  cout.clear();
}

/* run_zero_bound *************************************************************/
TEST_F(SimulatorTest, run_zero_bound)
{
  cout.setstate(ios_base::failbit);

  program.add(Instruction::Set::create("JMP", 0));

  simulator.create_thread(program);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0:
            {
              return simulator.threads[0];
            }
        case 1:
            {
              EXPECT_EQ(0, simulator.threads[0]->pc);

              return simulator.threads[0];
            }
        case 2:
            {
              /* 3 iterations are enough ... */
              simulator.bound = 1;

              EXPECT_EQ(0, simulator.threads[0]->pc);

              return simulator.threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator.run(scheduler);

  EXPECT_EQ(step, 3);

  EXPECT_EQ(Thread::State::RUNNING, simulator.threads[0]->state);

  /* check Schedule */
  ASSERT_EQ(0, schedule->exit);

  unordered_map<word, vector<word>> pcs({{0, {0, 0, 0}}});
  ASSERT_EQ(pcs, schedule->pcs);

  unordered_map<word, vector<word>> accus({{0, {0, 0, 0}}});
  ASSERT_EQ(accus, schedule->accus);

  unordered_map<word, vector<word>> mems({{0, {0, 0, 0}}});
  ASSERT_EQ(mems, schedule->mems);

  vector<unordered_map<word, word>> heap({{}, {}, {}});
  ASSERT_EQ(heap, schedule->heaps);

  cout.clear();
}

/* simulate_increment_sync ****************************************************/
TEST_F(SimulatorTest, simulate_increment_sync)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.sync.t2.k16.schedule");
  string expected((istreambuf_iterator<char>(schedule_file)),
                   istreambuf_iterator<char>());

  ProgramPtr
    increment_0(create_from_file<Program>("data/increment.sync.thread.0.asm")),
    increment_n(create_from_file<Program>("data/increment.sync.thread.n.asm"));

  simulator.create_thread(*increment_0);
  simulator.create_thread(*increment_n);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* run it */
  ASSERT_EQ(0, simulator.simulate(16)->exit);

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(expected, ss.str());
}

/* simulate_increment_cas *****************************************************/
TEST_F(SimulatorTest, simulate_increment_cas)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.cas.t2.k16.schedule");
  string expected((istreambuf_iterator<char>(schedule_file)),
                   istreambuf_iterator<char>());

  ProgramPtr increment(create_from_file<Program>("data/increment.cas.asm"));

  simulator.create_thread(*increment);
  simulator.create_thread(*increment);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* run it */
  ASSERT_EQ(0, simulator.simulate(16)->exit);

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(expected, ss.str());
}

/* replay_increment_sync ******************************************************/
TEST_F(SimulatorTest, replay_increment_sync)
{
  string schedule_file = "data/increment.sync.t2.k16.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string expected((istreambuf_iterator<char>(sfs)),
                   istreambuf_iterator<char>());
  sfs.clear();
  sfs.seekg(0, std::ios::beg);

  schedule = make_shared<Schedule>(sfs, schedule_file);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* replay */
  // NOTE: resetting this->simulator results in a failed test case!?
  Simulator sim = Simulator(schedule->programs);

  ASSERT_EQ(0, sim.replay(*schedule)->exit);

  ASSERT_EQ(1, sim.heap.size());
  ASSERT_EQ(2, sim.heap[0]);

  ASSERT_EQ(1, sim.threads[0]->accu);
  ASSERT_EQ(0, sim.threads[0]->mem);
  ASSERT_EQ(2, sim.threads[1]->accu);
  ASSERT_EQ(0, sim.threads[1]->mem);

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(expected, ss.str());
}

/* replay_increment_cas *******************************************************/
TEST_F(SimulatorTest, replay_increment_cas)
{
  string schedule_file = "data/increment.cas.t2.k16.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string expected((istreambuf_iterator<char>(sfs)),
                   istreambuf_iterator<char>());
  sfs.clear();
  sfs.seekg(0, std::ios::beg);

  schedule = make_shared<Schedule>(sfs, schedule_file);

  /* redirect stdout */
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  /* replay */
  // NOTE: resetting this->simulator results in a failed test case!?
  Simulator sim = Simulator(schedule->programs);

  ASSERT_EQ(0, sim.replay(*schedule)->exit);

  ASSERT_EQ(2, sim.heap[0]);

  ASSERT_EQ(1, sim.threads[0]->accu);
  ASSERT_EQ(1, sim.threads[0]->mem);
  ASSERT_EQ(0, sim.threads[1]->accu);
  ASSERT_EQ(0, sim.threads[1]->mem);

  redirecter.stop();

  /* compare output */
  ASSERT_EQ(expected, ss.str());
}

/* replay_programs_differ *****************************************************/
// TODO
TEST_F(SimulatorTest, replay_programs_differ)
{
  Simulator _simulator;

  Schedule _schedule;

  ProgramPtr
    p1 = make_shared<Program>(),
    p2 = make_shared<Program>();

  p1->path = "program_1.asm";
  p2->path = "program_2.asm";

  ProgramListPtr
    programs_simulator = make_shared<ProgramList>(),
    programs_schedule = make_shared<ProgramList>();

  /* number of programs differ */
  programs_simulator->push_back(p1);
  programs_simulator->push_back(p2);
  programs_schedule->push_back(p2);

  _simulator = Simulator(programs_simulator);
  _schedule = Schedule(programs_schedule, 1, 1);

  try
    {
      schedule = _simulator.replay(_schedule);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("number of programs differ [2, 1]", e.what());
    }

  /* programs differ */
  programs_simulator->clear();
  programs_simulator->push_back(p1);

  p1->add(Instruction::Set::create("ADDI", 1));
  p2->add(Instruction::Set::create("SUBI", 1));

  _simulator = Simulator(programs_simulator);
  _schedule = Schedule(programs_schedule, 1, 1);

  cout << p1->path << eol << p2->path << eol;

  try
    {
      schedule = _simulator.replay(_schedule);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_STREQ(
        "program #0 differs: program_1.asm != program_2.asm",
        e.what());
    }

  /* equal programs, different pointer */
  p2 = make_shared<Program>();
  p2->path = p1->path;

  p2->add(Instruction::Set::create("ADDI", 1));

  programs_schedule->clear();
  programs_schedule->push_back(p2);

  _simulator = Simulator(programs_simulator);
  _schedule = Schedule(programs_schedule, 1, 1);

  _schedule.push_back(0);

  schedule = _simulator.replay(_schedule);

  ASSERT_EQ(0, schedule->exit);
}
