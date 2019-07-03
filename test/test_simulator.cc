#include <gtest/gtest.h>

#include "simulator.hh"

#include "parser.hh"

namespace test {

//==============================================================================
// Simulator tests
//==============================================================================

struct Simulator : public ::testing::Test
{
  Program program;
  Schedule::ptr schedule;
  std::unique_ptr<::Simulator> simulator;

  void create_simulator(std::initializer_list<Program> programs)
    {
      simulator =
        std::make_unique<::Simulator>(
          std::make_shared<Program::List>(programs));
    }
};

// Simulator::create_thread ====================================================

TEST_F(Simulator, create_thread)
{
  create_simulator({});

  ASSERT_TRUE(simulator->active.empty());
  ASSERT_TRUE(simulator->threads.empty());
  ASSERT_TRUE(simulator->threads_per_checkpoint.empty());
  ASSERT_TRUE(simulator->waiting_for_checkpoint.empty());

  program.push_back(Instruction::create("ADDI", 1));

  simulator->create_thread(program);

  ASSERT_EQ(0, simulator->threads.back().id);
  ASSERT_TRUE(simulator->active.empty());
  ASSERT_EQ(1, simulator->threads.size());
  ASSERT_TRUE(simulator->threads_per_checkpoint.empty());
  ASSERT_TRUE(simulator->waiting_for_checkpoint.empty());

  program.push_back(Instruction::create("CHECK", 1));

  simulator->create_thread(program);

  ASSERT_EQ(1, simulator->threads.back().id);
  ASSERT_TRUE(simulator->active.empty());
  ASSERT_EQ(2, simulator->threads.size());
  ASSERT_EQ(1, simulator->threads_per_checkpoint[1].size());
  ASSERT_TRUE(simulator->waiting_for_checkpoint.empty());

  // basically tests mapped default value
  ASSERT_EQ(0, simulator->waiting_for_checkpoint[0]);
  ASSERT_TRUE(!simulator->waiting_for_checkpoint.empty());
}

// Simulator::run ==============================================================

TEST_F(Simulator, run_simple)
{
  program.push_back(Instruction::create("ADDI", 1));

  create_simulator({program, program});

  ASSERT_EQ(0, simulator->active.size());
  ASSERT_EQ(2, simulator->threads.size());
  ASSERT_TRUE(simulator->threads_per_checkpoint.empty());
  ASSERT_TRUE(simulator->waiting_for_checkpoint.empty());

  bound_t step = 0;

  // NOTE: EXPECT_* required by lambda std::function
  std::function<Thread *()> scheduler = [&] () -> Thread *
    {
      switch (step++)
        {
        case 0: // initial -> t0: pre ADDI 1
            {
              return &simulator->threads[0];
            }
        case 1: // t0: post ADDI 1 && next == t1
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(1, simulator->threads[0].accu);
              EXPECT_EQ(0, simulator->threads[1].pc);
              EXPECT_EQ(0, simulator->threads[1].accu);

              return &simulator->threads[1];
            }
        case 2: // t1: post ADDI 1 && next == t0
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(1, simulator->threads[0].accu);
              EXPECT_EQ(1, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);

              EXPECT_EQ(Thread::State::halted, simulator->threads[0].state);
              EXPECT_EQ(Thread::State::running, simulator->threads[1].state);

              return &simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  // run it
  schedule = simulator->run(scheduler);

  EXPECT_EQ(2, step);

  EXPECT_EQ(Thread::State::halted, simulator->threads[0].state);
  EXPECT_EQ(Thread::State::halted, simulator->threads[1].state);

  // check Schedule
  ASSERT_EQ(0, schedule->exit);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 1}}, {{2, 1}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}}),
    schedule->mem_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}}),
    schedule->sb_adr_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}}),
    schedule->sb_val_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<bool>({{{1, false}}, {{2, false}}}),
    schedule->sb_full_updates);

  ASSERT_EQ(Schedule::Flushes(), schedule->flushes);

  ASSERT_TRUE(schedule->heap_updates.empty());
}

TEST_F(Simulator, run_add_check_exit)
{
  program.push_back(Instruction::create("ADDI", 1));
  program.push_back(Instruction::create("CHECK", 1));
  program.push_back(Instruction::create("EXIT", 1));

  create_simulator({program, program});

  ASSERT_EQ(0, simulator->active.size());
  ASSERT_EQ(2, simulator->threads.size());
  ASSERT_EQ(2, simulator->threads_per_checkpoint[1].size());
  ASSERT_EQ(0, simulator->waiting_for_checkpoint[1]);

  bound_t step = 0;

  std::function<Thread *()> scheduler = [&] () -> Thread *
    {
      switch (step++)
        {
        case 0: // initial -> t0: pre ADDI 1
            {
              return &simulator->threads[0];
            }
        case 1: // t0: post ADDI 1 && next == t1
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(1, simulator->threads[0].accu);
              EXPECT_EQ(0, simulator->threads[1].pc);
              EXPECT_EQ(0, simulator->threads[1].accu);

              return &simulator->threads[1];
            }
        case 2: // t1: post ADDI 1 && next == t0
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(1, simulator->threads[0].accu);
              EXPECT_EQ(1, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);

              return &simulator->threads[0];
            }
        case 3: // t0: post CHECK 1 && next == t1
            {
              EXPECT_EQ(2, simulator->threads[0].pc);
              EXPECT_EQ(1, simulator->threads[0].accu);
              EXPECT_EQ(1, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);

              EXPECT_EQ(Thread::State::waiting, simulator->threads[0].state);
              EXPECT_EQ(Thread::State::running, simulator->threads[1].state);

              EXPECT_EQ(1, simulator->active.size());
              EXPECT_EQ(1, simulator->waiting_for_checkpoint[1]);

              return &simulator->threads[1];
            }
        case 4: // t1: post CHECK 1 (both active again) && next == t0
            {
              EXPECT_EQ(2, simulator->threads[0].pc);
              EXPECT_EQ(1, simulator->threads[0].accu);
              EXPECT_EQ(2, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);

              EXPECT_EQ(Thread::State::running, simulator->threads[0].state);
              EXPECT_EQ(Thread::State::running, simulator->threads[1].state);

              EXPECT_EQ(2, simulator->active.size());
              EXPECT_EQ(0, simulator->waiting_for_checkpoint[1]);

              return &simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  // run it
  schedule = simulator->run(scheduler);

  EXPECT_EQ(step, 5);

  EXPECT_EQ(Thread::State::exited, simulator->threads[0].state);
  EXPECT_EQ(Thread::State::running, simulator->threads[1].state);

  // check Schedule
  ASSERT_EQ(1, schedule->exit);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}, {3, 1}, {5, 2}},
      {{2, 0}, {4, 1}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 1}}, {{2, 1}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}}),
    schedule->mem_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}}),
    schedule->sb_adr_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}}),
    schedule->sb_val_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<bool>({{{1, false}}, {{2, false}}}),
    schedule->sb_full_updates);

  ASSERT_EQ(Schedule::Flushes(), schedule->flushes);

  ASSERT_TRUE(schedule->heap_updates.empty());
}

TEST_F(Simulator, run_race_condition)
{
  program.push_back(Instruction::create("LOAD", 1));
  program.push_back(Instruction::create("ADDI", 1));
  program.push_back(Instruction::create("STORE", 1));
  program.push_back(Instruction::create("CHECK", 1));

  Program checker;

  checker.push_back(Instruction::create("CHECK", 1));
  checker.push_back(Instruction::create("LOAD", 1));
  checker.push_back(Instruction::create("SUBI", 2));
  checker.push_back(Instruction::create("JZ", 5));
  checker.push_back(Instruction::create("EXIT", 1));
  checker.push_back(Instruction::create("EXIT", 0));

  create_simulator({checker, program, program});

  ASSERT_EQ(0, simulator->active.size());
  ASSERT_EQ(3, simulator->threads.size());
  ASSERT_EQ(3, simulator->threads_per_checkpoint[1].size());
  ASSERT_EQ(0, simulator->waiting_for_checkpoint[1]);

  bound_t step = 0;

  std::function<Thread *()> scheduler = [&] () -> Thread *
    {
      switch (step++)
        {
        case 0: // initial = t0 [CHECK 1]
            {
              EXPECT_EQ(0, simulator->heap[1]);

              EXPECT_EQ(0, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(0, simulator->threads[1].pc);
              EXPECT_EQ(0, simulator->threads[1].accu);
              EXPECT_EQ(0, simulator->threads[2].pc);
              EXPECT_EQ(0, simulator->threads[2].accu);

              EXPECT_EQ(3, simulator->active.size());

              return &simulator->threads[0];
            }
        case 1: // prev = t0 [CHECK 1] | next = t1 [LOAD 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(0, simulator->threads[1].pc);
              EXPECT_EQ(0, simulator->threads[1].accu);
              EXPECT_EQ(0, simulator->threads[2].pc);
              EXPECT_EQ(0, simulator->threads[2].accu);

              EXPECT_EQ(2, simulator->active.size());
              EXPECT_EQ(1, simulator->waiting_for_checkpoint[1]);
              EXPECT_EQ(Thread::State::waiting, simulator->threads[0].state);

              return &simulator->threads[1];
            }
        case 2: // prev = t1 [LOAD 1] | next = t2 [LOAD 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(1, simulator->threads[1].pc);
              EXPECT_EQ(0, simulator->threads[1].accu);
              EXPECT_EQ(0, simulator->threads[2].pc);
              EXPECT_EQ(0, simulator->threads[2].accu);

              return &simulator->threads[2];
            }
        case 3: // prev = t2 [LOAD 1] | next = t1 [ADDI 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(1, simulator->threads[1].pc);
              EXPECT_EQ(0, simulator->threads[1].accu);
              EXPECT_EQ(1, simulator->threads[2].pc);
              EXPECT_EQ(0, simulator->threads[2].accu);

              return &simulator->threads[1];
            }
        case 4: // prev = t1 [ADDI 1] | next = t2 [ADDI 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(2, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(1, simulator->threads[2].pc);
              EXPECT_EQ(0, simulator->threads[2].accu);

              return &simulator->threads[2];
            }
        case 5: // prev = t2 [ADDI 1] | next = t1 [STORE 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(2, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(2, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              return &simulator->threads[1];
            }
        case 6: // prev = t1 [STORE 1] | next = t2 [STORE 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(3, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(2, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              EXPECT_EQ(1, simulator->threads[1].buffer.address);
              EXPECT_EQ(1, simulator->threads[1].buffer.value);
              EXPECT_TRUE(simulator->threads[1].buffer.full);

              return &simulator->threads[2];
            }
        case 7: // prev = t2 [STORE 1] | next = t1 [FLUSH]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(3, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(3, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              EXPECT_EQ(1, simulator->threads[2].buffer.address);
              EXPECT_EQ(1, simulator->threads[2].buffer.value);
              EXPECT_TRUE(simulator->threads[2].buffer.full);

              simulator->threads[1].state = Thread::State::flushing;

              return &simulator->threads[1];
            }
        case 8: // prev = t1 [FLUSH] | next = t2 [FLUSH]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(3, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(3, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              EXPECT_FALSE(simulator->threads[1].buffer.full);

              EXPECT_EQ(
                simulator->threads[1].buffer.value,
                simulator->heap[simulator->threads[1].buffer.address]);

              simulator->threads[2].state = Thread::State::flushing;

              return &simulator->threads[2];
            }
        case 9: // prev = t2 [FLUSH] | next = t1 [CHECK 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(3, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(3, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              EXPECT_FALSE(simulator->threads[2].buffer.full);

              EXPECT_EQ(
                simulator->threads[2].buffer.value,
                simulator->heap[simulator->threads[2].buffer.address]);

              return &simulator->threads[1];
            }
        case 10: // prev = t1 [CHECK 1] | next = t2 [CHECK 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(4, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(3, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              EXPECT_EQ(1, simulator->active.size());
              EXPECT_EQ(1, simulator->waiting_for_checkpoint[1]);
              EXPECT_EQ(Thread::State::waiting, simulator->threads[0].state);
              EXPECT_EQ(Thread::State::halted, simulator->threads[1].state);

              return &simulator->threads[2];
            }
        case 11: // prev = t2 [CHECK 1] | next = t0 [LOAD 1]
            {
              EXPECT_EQ(1, simulator->threads[0].pc);
              EXPECT_EQ(0, simulator->threads[0].accu);
              EXPECT_EQ(4, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(4, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              EXPECT_EQ(1, simulator->active.size());
              EXPECT_EQ(0, simulator->waiting_for_checkpoint[1]);
              EXPECT_EQ(Thread::State::running, simulator->threads[0].state);
              EXPECT_EQ(Thread::State::halted, simulator->threads[1].state);
              EXPECT_EQ(Thread::State::halted, simulator->threads[2].state);

              return &simulator->threads[0];
            }
        case 12: // prev = t0 [LOAD 1] | next = t0 [SUBI 2]
            {
              EXPECT_EQ(2, simulator->threads[0].pc);
              EXPECT_EQ(1, simulator->threads[0].accu);
              EXPECT_EQ(4, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(4, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              return &simulator->threads[0];
            }
        case 13: // prev = t0 [SUBI 2] | next = t0 [JZ 5]
            {
              EXPECT_EQ(3, simulator->threads[0].pc);
              EXPECT_EQ(word_t(-1), simulator->threads[0].accu);
              EXPECT_EQ(4, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(4, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              return &simulator->threads[0];
            }
        case 14: // prev = t0 [JZ 5] | next = t0 [EXIT 1]
            {
              EXPECT_EQ(4, simulator->threads[0].pc);
              EXPECT_EQ(word_t(-1), simulator->threads[0].accu);
              EXPECT_EQ(4, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(4, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              return &simulator->threads[0];
            }
        case 15: // last = t0 [EXIT 1]
            {
              EXPECT_EQ(4, simulator->threads[0].pc);
              EXPECT_EQ(word_t(-1), simulator->threads[0].accu);
              EXPECT_EQ(4, simulator->threads[1].pc);
              EXPECT_EQ(1, simulator->threads[1].accu);
              EXPECT_EQ(4, simulator->threads[2].pc);
              EXPECT_EQ(1, simulator->threads[2].accu);

              EXPECT_EQ(Thread::State::exited, simulator->threads[0].state);

              return &simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have exited by now";
              return nullptr;
            }
        }
    };

  // run it
  schedule = simulator->run(scheduler);

  EXPECT_EQ(15, step);

  EXPECT_EQ(Thread::State::exited, simulator->threads[0].state);
  EXPECT_EQ(Thread::State::halted, simulator->threads[1].state);
  EXPECT_EQ(Thread::State::halted, simulator->threads[2].state);

  // check Schedule
  ASSERT_EQ(1, schedule->exit);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}, {12, 1}, {13, 2}, {14, 3}, {15, 4}},
      {{2, 0}, {4, 1}, {6, 2}, {10, 3}},
      {{3, 0}, {5, 1}, {7, 2}, {11, 3}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}, {12, 1}, {13, 65535}, {15, 1}},
      {{2, 0}, {4, 1}},
      {{3, 0}, {5, 1}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}, {{2, 0}}, {{3, 0}}}),
    schedule->mem_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}, {6, 1}},
      {{3, 0}, {7, 1}}}),
    schedule->sb_adr_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}, {6, 1}},
      {{3, 0}, {7, 1}}}),
    schedule->sb_val_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<bool>({
      {{1, false}},
      {{2, false}, {6, true}, {8, false}},
      {{3, false}, {7, true}, {9, false}}}),
    schedule->sb_full_updates);

  ASSERT_EQ(Schedule::Flushes({8, 9}), schedule->flushes);

  ASSERT_EQ(
    Schedule::Heap_Updates({{1, {{8, 1}}}}),
    schedule->heap_updates);
}

TEST_F(Simulator, run_zero_bound)
{
  program.push_back(Instruction::create("JMP", 0));

  create_simulator({program});

  bound_t step = 0;

  std::function<Thread *()> scheduler = [&] () -> Thread *
    {
      switch (step++)
        {
        case 0:
            {
              return &simulator->threads[0];
            }
        case 1:
            {
              EXPECT_EQ(0, simulator->threads[0].pc);

              return &simulator->threads[0];
            }
        case 2:
            {
              // 3 iterations are enough ...
              simulator->bound = 1;

              EXPECT_EQ(0, simulator->threads[0].pc);

              return &simulator->threads[0];
            }
        default:
            {
              EXPECT_TRUE(false) << "should have halted by now";
              return nullptr;
            }
        }
    };

  // run it
  schedule = simulator->run(scheduler);

  EXPECT_EQ(step, 3);

  EXPECT_EQ(Thread::State::running, simulator->threads[0].state);

  // check Schedule
  ASSERT_EQ(0, schedule->exit);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}}),
    schedule->pc_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}}),
    schedule->accu_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}}),
    schedule->mem_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}}),
    schedule->sb_adr_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({{{1, 0}}}),
    schedule->sb_val_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<bool>({{{1, false}}}),
    schedule->sb_full_updates);

  ASSERT_EQ(Schedule::Flushes(), schedule->flushes);

  ASSERT_TRUE(schedule->heap_updates.empty());
}

// Simulator::simulate =========================================================

TEST_F(Simulator, simulate_increment_check)
{
  std::ifstream schedule_file("data/increment.check.t2.k16.schedule");
  std::string expected((std::istreambuf_iterator<char>(schedule_file)),
                        std::istreambuf_iterator<char>());

  Program::List::ptr programs = std::make_shared<Program::List>();
  programs->push_back(
    create_from_file<Program>("data/increment.check.thread.0.asm"));
  programs->push_back(
    create_from_file<Program>("data/increment.check.thread.n.asm"));

  schedule = ::Simulator::simulate(programs, 16);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
}

TEST_F(Simulator, simulate_increment_cas)
{
  std::ifstream schedule_file("data/increment.cas.t2.k16.schedule");
  std::string expected((std::istreambuf_iterator<char>(schedule_file)),
                        std::istreambuf_iterator<char>());

  Program increment = create_from_file<Program>("data/increment.cas.asm");

  Program::List::ptr programs = std::make_shared<Program::List>();
  programs->push_back(increment);
  programs->push_back(increment);

  schedule = ::Simulator::simulate(programs, 16);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
}

// Simulator::replay ===========================================================

TEST_F(Simulator, replay_increment_check)
{
  std::string schedule_file = "data/increment.check.t2.k16.schedule";

  std::ifstream sfs(schedule_file);
  std::string expected((std::istreambuf_iterator<char>(sfs)),
                        std::istreambuf_iterator<char>());
  sfs.clear();
  sfs.seekg(0, std::ios::beg);

  schedule = std::make_unique<Schedule>(sfs, schedule_file);

  schedule = ::Simulator::replay(*schedule);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
}

TEST_F(Simulator, replay_increment_cas)
{
  std::string schedule_file = "data/increment.cas.t2.k16.schedule";

  std::ifstream sfs(schedule_file);
  std::string expected((std::istreambuf_iterator<char>(sfs)),
                        std::istreambuf_iterator<char>());
  sfs.clear();
  sfs.seekg(0, std::ios::beg);

  schedule = std::make_unique<Schedule>(sfs, schedule_file);

  schedule = ::Simulator::replay(*schedule);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->bound);
  ASSERT_EQ(expected, schedule->print());
}

} // namespace test
