#include <gtest/gtest.h>

#include "parser.hh"
#include "simulator.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct SimulatorTest : public ::testing::Test
{
  ProgramPtr    program = make_shared<Program>();
  SchedulePtr   schedule;
  SimulatorPtr  simulator;

  void create_simulator(initializer_list<ProgramPtr> programs)
    {
      simulator = make_shared<Simulator>(make_shared<ProgramList>(programs));
    }
};

/* activate_threads ***********************************************************/
TEST_F(SimulatorTest, activate_threads)
{
  simulator = make_shared<Simulator>();

  ASSERT_TRUE(simulator->active.empty());
  ASSERT_TRUE(simulator->threads.empty());

  program->push_back(Instruction::Set::create("ADDI", 1));

  simulator->create_thread(*program);

  ASSERT_TRUE(simulator->active.empty());
  ASSERT_EQ(1, simulator->threads.size());
  ASSERT_EQ(Thread::State::INITIAL, simulator->threads[0]->state);

  simulator->activate_threads(simulator->threads);

  ASSERT_EQ(1, simulator->active.size());
  ASSERT_EQ(Thread::State::RUNNING, simulator->active[0]->state);
  ASSERT_EQ(simulator->threads[0], simulator->active[0]);
}

/* create_thread **************************************************************/
TEST_F(SimulatorTest, create_thread)
{
  simulator = make_shared<Simulator>();

  ASSERT_TRUE(simulator->active.empty());
  ASSERT_TRUE(simulator->threads.empty());
  ASSERT_TRUE(simulator->threads_per_sync_id.empty());
  ASSERT_TRUE(simulator->waiting_per_sync_id.empty());

  program->push_back(Instruction::Set::create("ADDI", 1));

  simulator->create_thread(*program);

  ASSERT_EQ(0, simulator->threads.back()->id);
  ASSERT_TRUE(simulator->active.empty());
  ASSERT_EQ(1, simulator->threads.size());
  ASSERT_TRUE(simulator->threads_per_sync_id.empty());
  ASSERT_TRUE(simulator->waiting_per_sync_id.empty());

  program->push_back(Instruction::Set::create("SYNC", 1));

  simulator->create_thread(*program);

  ASSERT_EQ(1, simulator->threads.back()->id);
  ASSERT_TRUE(simulator->active.empty());
  ASSERT_EQ(2, simulator->threads.size());
  ASSERT_EQ(1, simulator->threads_per_sync_id[1].size());
  ASSERT_TRUE(simulator->waiting_per_sync_id.empty());

  /* basically tests mapped default value */
  ASSERT_EQ(0, simulator->waiting_per_sync_id[0]);
  ASSERT_TRUE(!simulator->waiting_per_sync_id.empty());
}

/* run_simple *****************************************************************/
TEST_F(SimulatorTest, run_simple)
{
  program->push_back(Instruction::Set::create("ADDI", 1));

  create_simulator({program, program});

  ASSERT_EQ(0, simulator->active.size());
  ASSERT_EQ(2, simulator->threads.size());
  ASSERT_TRUE(simulator->threads_per_sync_id.empty());
  ASSERT_TRUE(simulator->waiting_per_sync_id.empty());

  unsigned long step = 0;

  /* NOTE: EXPECT_* required by lambda function */
  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial -> t0: pre ADDI 1 */
            {
              return simulator->threads[0];
            }
        case 1: /* t0: post ADDI 1 && next == t1 */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(1, simulator->threads[0]->accu);
              EXPECT_EQ(0, simulator->threads[1]->pc);
              EXPECT_EQ(0, simulator->threads[1]->accu);

              return simulator->threads[1];
            }
        case 2: /* t1: post ADDI 1 && next == t0 */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(1, simulator->threads[0]->accu);
              EXPECT_EQ(1, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);

              EXPECT_EQ(Thread::State::STOPPED, simulator->threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, simulator->threads[1]->state);

              return simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator->run(scheduler);

  EXPECT_EQ(2, step);

  EXPECT_EQ(Thread::State::STOPPED, simulator->threads[0]->state);
  EXPECT_EQ(Thread::State::STOPPED, simulator->threads[1]->state);

  /* check Schedule */
  ASSERT_EQ(0, schedule->exit);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 0}},
      {{2, 0}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 1}},
      {{2, 1}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 0}},
      {{2, 0}}}),
    schedule->mem_updates);

  ASSERT_TRUE(schedule->heap_updates.empty());
}

/* run_add_sync_exit **********************************************************/
TEST_F(SimulatorTest, run_add_sync_exit)
{
  program->push_back(Instruction::Set::create("ADDI", 1));
  program->push_back(Instruction::Set::create("SYNC", 1));
  program->push_back(Instruction::Set::create("EXIT", 1));

  create_simulator({program, program});

  ASSERT_EQ(0, simulator->active.size());
  ASSERT_EQ(2, simulator->threads.size());
  ASSERT_EQ(2, simulator->threads_per_sync_id[1].size());
  ASSERT_EQ(0, simulator->waiting_per_sync_id[1]);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial -> t0: pre ADDI 1 */
            {
              return simulator->threads[0];
            }
        case 1: /* t0: post ADDI 1 && next == t1 */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(1, simulator->threads[0]->accu);
              EXPECT_EQ(0, simulator->threads[1]->pc);
              EXPECT_EQ(0, simulator->threads[1]->accu);

              return simulator->threads[1];
            }
        case 2: /* t1: post ADDI 1 && next == t0 */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(1, simulator->threads[0]->accu);
              EXPECT_EQ(1, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);

              return simulator->threads[0];
            }
        case 3: /* t0: post SYNC 1 && next == t1 */
            {
              EXPECT_EQ(2, simulator->threads[0]->pc);
              EXPECT_EQ(1, simulator->threads[0]->accu);
              EXPECT_EQ(1, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);

              EXPECT_EQ(Thread::State::WAITING, simulator->threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, simulator->threads[1]->state);

              EXPECT_EQ(1, simulator->active.size());
              EXPECT_EQ(1, simulator->waiting_per_sync_id[1]);

              return simulator->threads[1];
            }
        case 4: /* t1: post SYNC 1 (both active again) && next == t0 */
            {
              EXPECT_EQ(2, simulator->threads[0]->pc);
              EXPECT_EQ(1, simulator->threads[0]->accu);
              EXPECT_EQ(2, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);

              EXPECT_EQ(Thread::State::RUNNING, simulator->threads[0]->state);
              EXPECT_EQ(Thread::State::RUNNING, simulator->threads[1]->state);

              EXPECT_EQ(2, simulator->active.size());
              EXPECT_EQ(0, simulator->waiting_per_sync_id[1]);

              return simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator->run(scheduler);

  EXPECT_EQ(step, 5);

  EXPECT_EQ(Thread::State::EXITING, simulator->threads[0]->state);
  EXPECT_EQ(Thread::State::RUNNING, simulator->threads[1]->state);

  /* check Schedule */
  ASSERT_EQ(1, schedule->exit);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 0}, {3, 1}, {5, 2}},
      {{2, 0}, {4, 1}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 1}},
      {{2, 1}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 0}},
      {{2, 0}}}),
    schedule->mem_updates);

  ASSERT_TRUE(schedule->heap_updates.empty());
}

/* run_race_condition *********************************************************/
TEST_F(SimulatorTest, run_race_condition)
{
  program->push_back(Instruction::Set::create("LOAD", 1));
  program->push_back(Instruction::Set::create("ADDI", 1));
  program->push_back(Instruction::Set::create("STORE", 1));
  program->push_back(Instruction::Set::create("SYNC", 1));

  ProgramPtr checker = make_shared<Program>();

  checker->push_back(Instruction::Set::create("SYNC", 1));
  checker->push_back(Instruction::Set::create("LOAD", 1));
  checker->push_back(Instruction::Set::create("SUBI", 2));
  checker->push_back(Instruction::Set::create("JZ", 5));
  checker->push_back(Instruction::Set::create("EXIT", 1));
  checker->push_back(Instruction::Set::create("EXIT", 0));

  create_simulator({checker, program, program});

  ASSERT_EQ(0, simulator->active.size());
  ASSERT_EQ(3, simulator->threads.size());
  ASSERT_EQ(3, simulator->threads_per_sync_id[1].size());
  ASSERT_EQ(0, simulator->waiting_per_sync_id[1]);

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0: /* initial = t0 [SYNC 1] */
            {
              EXPECT_EQ(0, simulator->heap[1]);

              EXPECT_EQ(0, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(0, simulator->threads[1]->pc);
              EXPECT_EQ(0, simulator->threads[1]->accu);
              EXPECT_EQ(0, simulator->threads[2]->pc);
              EXPECT_EQ(0, simulator->threads[2]->accu);

              EXPECT_EQ(3, simulator->active.size());

              return simulator->threads[0];
            }
        case 1: /* prev = t0 [SYNC 1] | next = t1 [LOAD 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(0, simulator->threads[1]->pc);
              EXPECT_EQ(0, simulator->threads[1]->accu);
              EXPECT_EQ(0, simulator->threads[2]->pc);
              EXPECT_EQ(0, simulator->threads[2]->accu);

              EXPECT_EQ(2, simulator->active.size());
              EXPECT_EQ(1, simulator->waiting_per_sync_id[1]);
              EXPECT_EQ(Thread::State::WAITING, simulator->threads[0]->state);

              return simulator->threads[1];
            }
        case 2: /* prev = t1 [LOAD 1] | next = t2 [LOAD 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(1, simulator->threads[1]->pc);
              EXPECT_EQ(0, simulator->threads[1]->accu);
              EXPECT_EQ(0, simulator->threads[2]->pc);
              EXPECT_EQ(0, simulator->threads[2]->accu);

              return simulator->threads[2];
            }
        case 3: /* prev = t2 [LOAD 1] | next = t1 [ADDI 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(1, simulator->threads[1]->pc);
              EXPECT_EQ(0, simulator->threads[1]->accu);
              EXPECT_EQ(1, simulator->threads[2]->pc);
              EXPECT_EQ(0, simulator->threads[2]->accu);

              return simulator->threads[1];
            }
        case 4: /* prev = t1 [ADDI 1] | next = t2 [ADDI 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(2, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(1, simulator->threads[2]->pc);
              EXPECT_EQ(0, simulator->threads[2]->accu);

              return simulator->threads[2];
            }
        case 5: /* prev = t2 [ADDI 1] | next = t1 [STORE 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(2, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(2, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              return simulator->threads[1];
            }
        case 6: /* prev = t1 [STORE 1] | next = t2 [STORE 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(3, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(2, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              EXPECT_EQ(1, simulator->heap[1]);

              return simulator->threads[2];
            }
        case 7: /* prev = t2 [STORE 1] | next = t1 [SYNC 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(3, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(3, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              EXPECT_EQ(1, simulator->heap[1]);

              return simulator->threads[1];
            }
        case 8: /* prev = t1 [SYNC 1] | next = t2 [SYNC 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(4, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(3, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              EXPECT_EQ(1, simulator->active.size());
              EXPECT_EQ(1, simulator->waiting_per_sync_id[1]);
              EXPECT_EQ(Thread::State::WAITING, simulator->threads[0]->state);
              EXPECT_EQ(Thread::State::STOPPED, simulator->threads[1]->state);

              return simulator->threads[2];
            }
        case 9: /* prev = t2 [SYNC 1] | next = t0 [LOAD 1] */
            {
              EXPECT_EQ(1, simulator->threads[0]->pc);
              EXPECT_EQ(0, simulator->threads[0]->accu);
              EXPECT_EQ(4, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(4, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              EXPECT_EQ(1, simulator->active.size());
              EXPECT_EQ(0, simulator->waiting_per_sync_id[1]);
              EXPECT_EQ(Thread::State::RUNNING, simulator->threads[0]->state);
              EXPECT_EQ(Thread::State::STOPPED, simulator->threads[1]->state);
              EXPECT_EQ(Thread::State::STOPPED, simulator->threads[2]->state);

              return simulator->threads[0];
            }
        case 10: /* prev = t0 [LOAD 1] | next = t0 [SUBI 2] */
            {
              EXPECT_EQ(2, simulator->threads[0]->pc);
              EXPECT_EQ(1, simulator->threads[0]->accu);
              EXPECT_EQ(4, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(4, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              return simulator->threads[0];
            }
        case 11: /* prev = t0 [SUBI 2] | next = t0 [JZ 5] */
            {
              EXPECT_EQ(3, simulator->threads[0]->pc);
              EXPECT_EQ(word(-1), simulator->threads[0]->accu);
              EXPECT_EQ(4, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(4, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              return simulator->threads[0];
            }
        case 12: /* prev = t0 [JZ 5] | next = t0 [EXIT 1] */
            {
              EXPECT_EQ(4, simulator->threads[0]->pc);
              EXPECT_EQ(word(-1), simulator->threads[0]->accu);
              EXPECT_EQ(4, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(4, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              return simulator->threads[0];
            }
        case 13: /* last = t0 [EXIT 1] */
            {
              EXPECT_EQ(4, simulator->threads[0]->pc);
              EXPECT_EQ(word(-1), simulator->threads[0]->accu);
              EXPECT_EQ(4, simulator->threads[1]->pc);
              EXPECT_EQ(1, simulator->threads[1]->accu);
              EXPECT_EQ(4, simulator->threads[2]->pc);
              EXPECT_EQ(1, simulator->threads[2]->accu);

              EXPECT_EQ(Thread::State::EXITING, simulator->threads[0]->state);

              return simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator->run(scheduler);

  EXPECT_EQ(13, step);

  EXPECT_EQ(Thread::State::EXITING, simulator->threads[0]->state);
  EXPECT_EQ(Thread::State::STOPPED, simulator->threads[1]->state);
  EXPECT_EQ(Thread::State::STOPPED, simulator->threads[2]->state);

  /* check Schedule */
  ASSERT_EQ(1, schedule->exit);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 0}, {10, 1}, {11, 2}, {12, 3}, {13, 4}},
      {{2, 0}, {4, 1}, {6, 2}, {8, 3}},
      {{3, 0}, {5, 1}, {7, 2}, {9, 3}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({
      {{1, 0}, {10, 1}, {11, 65535}, {13, 1}},
      {{2, 0}, {4, 1}},
      {{3, 0}, {5, 1}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({{{1, 0}}, {{2, 0}}, {{3, 0}}}),
    schedule->mem_updates);

  ASSERT_EQ(
    Schedule::heap_updates_t({{1, {{6, 1}}}}),
    schedule->heap_updates);
}

/* run_zero_bound *************************************************************/
TEST_F(SimulatorTest, run_zero_bound)
{
  program->push_back(Instruction::Set::create("JMP", 0));

  create_simulator({program});

  unsigned long step = 0;

  function<ThreadPtr(void)> scheduler = [&]()->ThreadPtr
    {
      switch (step++)
        {
        case 0:
            {
              return simulator->threads[0];
            }
        case 1:
            {
              EXPECT_EQ(0, simulator->threads[0]->pc);

              return simulator->threads[0];
            }
        case 2:
            {
              /* 3 iterations are enough ... */
              simulator->bound = 1;

              EXPECT_EQ(0, simulator->threads[0]->pc);

              return simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  /* run it */
  schedule = simulator->run(scheduler);

  EXPECT_EQ(step, 3);

  EXPECT_EQ(Thread::State::RUNNING, simulator->threads[0]->state);

  /* check Schedule */
  ASSERT_EQ(0, schedule->exit);

  ASSERT_EQ(
    Schedule::thread_updates_t({{{1, 0}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({{{1, 0}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::thread_updates_t({{{1, 0}}}),
    schedule->mem_updates);

  ASSERT_TRUE(schedule->heap_updates.empty());
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

  create_simulator({increment_0, increment_n});

  /* run it */
  schedule = simulator->simulate(16);

  /* compare output */
  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
}

/* simulate_increment_cas *****************************************************/
TEST_F(SimulatorTest, simulate_increment_cas)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.cas.t2.k16.schedule");
  string expected((istreambuf_iterator<char>(schedule_file)),
                   istreambuf_iterator<char>());

  ProgramPtr increment(create_from_file<Program>("data/increment.cas.asm"));

  create_simulator({increment, increment});

  /* run it */
  schedule = simulator->simulate(16);

  /* compare output */
  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
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
  simulator = make_shared<Simulator>(schedule->programs);

  /* replay */
  schedule = simulator->replay(*schedule);

  ASSERT_EQ(1, simulator->heap.size());
  ASSERT_EQ(2, simulator->heap[0]);

  ASSERT_EQ(1, simulator->threads[0]->accu);
  ASSERT_EQ(0, simulator->threads[0]->mem);
  ASSERT_EQ(2, simulator->threads[1]->accu);
  ASSERT_EQ(0, simulator->threads[1]->mem);

  /* compare output */
  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
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
  simulator = make_shared<Simulator>(schedule->programs);

  /* replay */
  schedule = simulator->replay(*schedule);

  ASSERT_EQ(1, simulator->heap.size());
  ASSERT_EQ(2, simulator->heap[0]);

  ASSERT_EQ(1, simulator->threads[0]->accu);
  ASSERT_EQ(1, simulator->threads[0]->mem);
  ASSERT_EQ(0, simulator->threads[1]->accu);
  ASSERT_EQ(0, simulator->threads[1]->mem);

  /* compare output */
  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
}

/* replay_programs_differ *****************************************************/
TEST_F(SimulatorTest, replay_programs_differ)
{
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

  simulator = make_shared<Simulator>(programs_simulator);
  schedule = make_shared<Schedule>(programs_schedule);

  try
    {
      schedule = simulator->replay(*schedule);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("number of programs differ [2, 1]", e.what());
    }

  /* programs differ */
  programs_simulator->clear();
  programs_simulator->push_back(p1);

  p1->push_back(Instruction::Set::create("ADDI", 1));
  p2->push_back(Instruction::Set::create("SUBI", 1));

  simulator = make_shared<Simulator>(programs_simulator);
  schedule = make_shared<Schedule>(programs_schedule);

  try
    {
      schedule = simulator->replay(*schedule);
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

  p2->push_back(Instruction::Set::create("ADDI", 1));

  programs_schedule->clear();
  programs_schedule->push_back(p2);

  simulator = make_shared<Simulator>(programs_simulator);
  schedule = make_shared<Schedule>(programs_schedule);

  schedule->push_back(0, 0, 1, 0, {});

  schedule = simulator->replay(*schedule);

  ASSERT_EQ(0, schedule->exit);
}
