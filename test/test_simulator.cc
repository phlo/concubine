#include <gtest/gtest.h>

#include "simulator.hh"

#include "mmap.hh"
#include "parser.hh"

namespace ConcuBinE::test {

//==============================================================================
// Simulator tests
//==============================================================================

struct Simulator : public ::testing::Test
{
  using State = ConcuBinE::Simulator::State;

  Program program;
  std::unique_ptr<Trace> trace;
  ConcuBinE::Simulator simulator;

  void init (std::initializer_list<Program> programs, MMap && mmap = {})
    {
      simulator.init(
          std::make_shared<Program::List>(programs),
          std::make_shared<MMap>(mmap),
          0);
    }
};

// Simulator::run ==============================================================

TEST_F(Simulator, run_simple)
{
  program.push_back(Instruction::create("ADDI", 1));
  program.push_back(Instruction::create("HALT"));

  init({program, program});

  ASSERT_EQ(2, simulator.active.size());
  ASSERT_EQ(2, simulator.programs->size());
  ASSERT_TRUE(simulator.threads_per_checkpoint.empty());
  ASSERT_TRUE(simulator.waiting_for_checkpoint.empty());

  // NOTE: EXPECT_* required by lambda std::function
  trace = simulator.run([this] () {
    switch (simulator.step)
      {
      case 0: simulator.thread = 0; break;
      case 1: // t0: post ADDI 1 && next == t1
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(0, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->accu(1));

          simulator.thread = 1;
          break;
        }
      case 2: // t1: post ADDI 1 && next == t0
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));

          EXPECT_EQ(State::running, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          simulator.thread = 0;
          break;
        }
      case 3: // t0: post HALT && next == t1
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));

          EXPECT_EQ(State::halted, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          simulator.thread = 1;
          break;
        }
      default: FAIL() << "should have halted by now";
      }
  });

  ASSERT_EQ(trace->size(), simulator.step);

  ASSERT_EQ(State::halted, simulator.state[0]);
  ASSERT_EQ(State::halted, simulator.state[1]);

  // check Trace
  ASSERT_EQ(0, trace->exit);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}},
      {{0, 0}, {2, 1}}}),
    trace->pc_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}},
      {{0, 0}, {2, 1}}}),
    trace->accu_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}, {{0, 0}}}),
    trace->mem_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}, {{0, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}, {{0, 0}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    Trace::thread_map<bool>({{{0, false}}, {{0, false}}}),
    trace->sb_full_updates);

  ASSERT_TRUE(trace->flushes.empty());

  ASSERT_TRUE(trace->heap_adr_updates.empty());
  ASSERT_TRUE(trace->heap_val_updates.empty());
}

TEST_F(Simulator, run_add_check_exit)
{
  program.push_back(Instruction::create("ADDI", 1));
  program.push_back(Instruction::create("CHECK", 1));
  program.push_back(Instruction::create("EXIT", 1));

  init({program, program});

  ASSERT_EQ(2, simulator.active.size());
  ASSERT_EQ(2, simulator.programs->size());
  ASSERT_EQ(2, simulator.threads_per_checkpoint[1].size());
  ASSERT_EQ(0, simulator.waiting_for_checkpoint[1]);

  // run it
  trace = simulator.run([this] () {
    switch (simulator.step)
      {
      case 0: simulator.thread = 0; break;
      case 1: // t0: post ADDI 1 && next == t1
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(0, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->accu(1));

          simulator.thread = 1;
          break;
        }
      case 2: // t1: post ADDI 1 && next == t0
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));

          simulator.thread = 0;
          break;
        }
      case 3: // t0: post CHECK 1 && next == t1
        {
          EXPECT_EQ(2, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));

          EXPECT_EQ(State::waiting, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          EXPECT_EQ(1, simulator.active.size());
          EXPECT_EQ(1, simulator.waiting_for_checkpoint[1]);

          simulator.thread = 1;
          break;
        }
      case 4: // t1: post CHECK 1 (both active again) && next == t0
        {
          EXPECT_EQ(2, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(2, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));

          EXPECT_EQ(State::running, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          EXPECT_EQ(2, simulator.active.size());
          EXPECT_EQ(0, simulator.waiting_for_checkpoint[1]);

          simulator.thread = 0;
          break;
        }
      default: FAIL() << "should have exited by now";
      }
  });

  ASSERT_EQ(trace->size(), simulator.step);

  ASSERT_EQ(State::exited, simulator.state[0]);
  ASSERT_EQ(State::running, simulator.state[1]);

  // check Trace
  ASSERT_EQ(1, trace->exit);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}, {3, 2}},
      {{0, 0}, {2, 1}, {4, 2}}}),
    trace->pc_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}},
      {{0, 0}, {2, 1}}}),
    trace->accu_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}, {{0, 0}}}),
    trace->mem_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}, {{0, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}, {{0, 0}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    Trace::thread_map<bool>({{{0, false}}, {{0, false}}}),
    trace->sb_full_updates);

  ASSERT_TRUE(trace->flushes.empty());

  ASSERT_TRUE(trace->heap_adr_updates.empty());
  ASSERT_TRUE(trace->heap_val_updates.empty());
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

  init({checker, program, program}, {{1, 0}});

  ASSERT_EQ(3, simulator.active.size());
  ASSERT_EQ(3, simulator.programs->size());
  ASSERT_EQ(3, simulator.threads_per_checkpoint[1].size());
  ASSERT_EQ(0, simulator.waiting_for_checkpoint[1]);

  // run it
  trace = simulator.run([this] () {
    switch (simulator.step)
      {
      case 0: // initial = t0 [CHECK 1]
        {
          EXPECT_EQ(0, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(0, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->accu(1));
          EXPECT_EQ(0, simulator.trace->pc(2));
          EXPECT_EQ(0, simulator.trace->accu(2));

          EXPECT_EQ(3, simulator.active.size());

          simulator.thread = 0;
          break;
        }
      case 1: // prev = t0 [CHECK 1] | next = t1 [LOAD 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(0, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->accu(1));
          EXPECT_EQ(0, simulator.trace->pc(2));
          EXPECT_EQ(0, simulator.trace->accu(2));

          EXPECT_EQ(2, simulator.active.size());
          EXPECT_EQ(1, simulator.waiting_for_checkpoint[1]);
          EXPECT_EQ(State::waiting, simulator.state[0]);

          simulator.thread = 1;
          break;
        }
      case 2: // prev = t1 [LOAD 1] | next = t2 [LOAD 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->accu(1));
          EXPECT_EQ(0, simulator.trace->pc(2));
          EXPECT_EQ(0, simulator.trace->accu(2));

          simulator.thread = 2;
          break;
        }
      case 3: // prev = t2 [LOAD 1] | next = t1 [ADDI 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->accu(1));
          EXPECT_EQ(1, simulator.trace->pc(2));
          EXPECT_EQ(0, simulator.trace->accu(2));

          simulator.thread = 1;
          break;
        }
      case 4: // prev = t1 [ADDI 1] | next = t2 [ADDI 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(2, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(1, simulator.trace->pc(2));
          EXPECT_EQ(0, simulator.trace->accu(2));

          simulator.thread = 2;
          break;
        }
      case 5: // prev = t2 [ADDI 1] | next = t1 [STORE 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(2, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(2, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          simulator.thread = 1;
          break;
        }
      case 6: // prev = t1 [STORE 1] | next = t2 [STORE 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(2, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          EXPECT_EQ(1, simulator.trace->sb_adr(1));
          EXPECT_EQ(1, simulator.trace->sb_val(1));
          EXPECT_TRUE(simulator.trace->sb_full(1));

          simulator.thread = 2;
          break;
        }
      case 7: // prev = t2 [STORE 1] | next = t1 [FLUSH]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          EXPECT_EQ(1, simulator.trace->sb_adr(2));
          EXPECT_EQ(1, simulator.trace->sb_val(2));
          EXPECT_TRUE(simulator.trace->sb_full(2));

          simulator.state[1] = State::flushing;

          simulator.thread = 1;
          break;
        }
      case 8: // prev = t1 [FLUSH] | next = t2 [FLUSH]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          EXPECT_FALSE(simulator.trace->sb_full(1));

          EXPECT_EQ(
            simulator.trace->sb_val(1),
            simulator.trace->heap(simulator.trace->sb_adr(1)));

          simulator.state[2] = State::flushing;

          simulator.thread = 2;
          break;
        }
      case 9: // prev = t2 [FLUSH] | next = t1 [CHECK 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          EXPECT_FALSE(simulator.trace->sb_full(2));

          EXPECT_EQ(
            simulator.trace->sb_val(2),
            simulator.trace->heap(simulator.trace->sb_adr(2)));

          simulator.thread = 1;
          break;
        }
      case 10: // prev = t1 [CHECK 1] | next = t2 [CHECK 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          EXPECT_EQ(1, simulator.active.size());
          EXPECT_EQ(2, simulator.waiting_for_checkpoint[1]);
          EXPECT_EQ(State::waiting, simulator.state[0]);
          EXPECT_EQ(State::halted, simulator.state[1]);

          simulator.thread = 2;
          break;
        }
      case 11: // prev = t2 [CHECK 1] | next = t0 [LOAD 1]
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          EXPECT_EQ(1, simulator.active.size());
          EXPECT_EQ(0, simulator.waiting_for_checkpoint[1]);
          EXPECT_EQ(State::running, simulator.state[0]);
          EXPECT_EQ(State::halted, simulator.state[1]);
          EXPECT_EQ(State::halted, simulator.state[2]);

          simulator.thread = 0;
          break;
        }
      case 12: // prev = t0 [LOAD 1] | next = t0 [SUBI 2]
        {
          EXPECT_EQ(2, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          simulator.thread = 0;
          break;
        }
      case 13: // prev = t0 [SUBI 2] | next = t0 [JZ 5]
        {
          EXPECT_EQ(3, simulator.trace->pc(0));
          EXPECT_EQ(word_t(-1), simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          simulator.thread = 0;
          break;
        }
      case 14: // prev = t0 [JZ 5] | next = t0 [EXIT 1]
        {
          EXPECT_EQ(4, simulator.trace->pc(0));
          EXPECT_EQ(word_t(-1), simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          simulator.thread = 0;
          break;
        }
      case 15: // last = t0 [EXIT 1]
        {
          EXPECT_EQ(4, simulator.trace->pc(0));
          EXPECT_EQ(word_t(-1), simulator.trace->accu(0));
          EXPECT_EQ(3, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(1));
          EXPECT_EQ(3, simulator.trace->pc(2));
          EXPECT_EQ(1, simulator.trace->accu(2));

          EXPECT_EQ(State::exited, simulator.state[0]);

          simulator.thread = 0;
          break;
        }
      default: FAIL() << "should have exited by now";
      }
  });

  ASSERT_EQ(trace->size(), simulator.step);

  ASSERT_EQ(State::exited, simulator.state[0]);
  ASSERT_EQ(State::halted, simulator.state[1]);
  ASSERT_EQ(State::halted, simulator.state[2]);

  // check Trace
  ASSERT_EQ(1, trace->exit);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}, {12, 2}, {13, 3}, {14, 4}},
      {{0, 0}, {2, 1}, {4, 2}, {6, 3}},
      {{0, 0}, {3, 1}, {5, 2}, {7, 3}}}),
    trace->pc_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {12, 1}, {13, 65535}},
      {{0, 0}, {4, 1}},
      {{0, 0}, {5, 1}}}),
    trace->accu_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}, {{0, 0}}, {{0, 0}}}),
    trace->mem_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}, {6, 1}},
      {{0, 0}, {7, 1}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}, {6, 1}},
      {{0, 0}, {7, 1}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    Trace::thread_map<bool>({
      {{0, false}},
      {{0, false}, {6, true}, {8, false}},
      {{0, false}, {7, true}, {9, false}}}),
    trace->sb_full_updates);

  ASSERT_EQ(std::unordered_set<size_t>({7, 8}), trace->flushes);

  ASSERT_EQ(
    Trace::update_map<word_t>({{8, 1}, {9, 1}}),
    trace->heap_adr_updates);
  ASSERT_EQ(
    Trace::heap_val_map({{1, {{8, 1}}}}),
    trace->heap_val_updates);
}

TEST_F(Simulator, run_zero_bound)
{
  program.push_back(Instruction::create("JMP", 0));

  init({program});

  // run it
  trace = simulator.run([this] () {
    switch (simulator.step)
      {
      case 0: simulator.thread = 0; break;
      case 1:
        {
          EXPECT_EQ(0, simulator.trace->pc(0));

          simulator.thread = 0;
          break;
        }
      case 2:
        {
          // 3 iterations are enough ...
          simulator.bound = 1;

          EXPECT_EQ(0, simulator.trace->pc(0));

          simulator.thread = 0;
          break;
        }
      default: FAIL() << "should have halted by now";
      }
  });

  EXPECT_EQ(trace->size(), simulator.step);

  EXPECT_EQ(State::running, simulator.state[0]);

  // check Trace
  ASSERT_EQ(0, trace->exit);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}}),
    trace->pc_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}}),
    trace->accu_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}}),
    trace->mem_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({{{0, 0}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    Trace::thread_map<bool>({{{0, false}}}),
    trace->sb_full_updates);

  ASSERT_TRUE(trace->flushes.empty());

  ASSERT_TRUE(trace->heap_adr_updates.empty());
  ASSERT_TRUE(trace->heap_val_updates.empty());
}

TEST_F(Simulator, run_final_thread)
{
  program.push_back(Instruction::create("ADDI", 1));
  program.push_back(Instruction::create("HALT"));

  init({program, program});

  simulator.bound = 2;

  // run it
  trace = simulator.run([this] () {
    switch (simulator.step)
      {
      case 0: simulator.thread = 0; break;
      case 1:
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(0, simulator.trace->accu(1));

          EXPECT_EQ(2, simulator.active.size());
          EXPECT_EQ(State::running, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          simulator.thread = 1;
          break;
        }
      case 2:
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(1, simulator.trace->accu(0));
          EXPECT_EQ(1, simulator.trace->accu(1));

          EXPECT_EQ(2, simulator.active.size());
          EXPECT_EQ(State::running, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          simulator.thread = 0;
          break;
        }
      default: FAIL() << "should have halted by now";
      }
  });

  ASSERT_EQ(trace->size(), simulator.step);

  ASSERT_EQ(State::running, simulator.state[0]);
  ASSERT_EQ(State::running, simulator.state[1]);

  // check Trace
  ASSERT_EQ(0, trace->exit);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}},
      {{0, 0}, {2, 1}}}),
    trace->pc_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}},
      {{0, 0}, {2, 1}}}),
    trace->accu_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}}}),
    trace->mem_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    Trace::thread_map<bool>({
      {{0, false}},
      {{0, false}}}),
    trace->sb_full_updates);

  ASSERT_TRUE(trace->flushes.empty());

  ASSERT_TRUE(trace->heap_adr_updates.empty());
  ASSERT_TRUE(trace->heap_val_updates.empty());
}

TEST_F(Simulator, run_final_flush)
{
  program.push_back(Instruction::create("STORE", 0));
  program.push_back(Instruction::create("HALT"));

  init({program, program});

  simulator.bound = 3;

  // run it
  trace = simulator.run([this] () {
    switch (simulator.step)
      {
      case 0: simulator.thread = 0; break;
      case 1:
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(0, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->sb_adr(0));
          EXPECT_EQ(0, simulator.trace->sb_adr(1));
          EXPECT_EQ(0, simulator.trace->sb_val(0));
          EXPECT_EQ(0, simulator.trace->sb_val(1));
          EXPECT_EQ(1, simulator.trace->sb_full(0));
          EXPECT_EQ(0, simulator.trace->sb_full(1));

          EXPECT_EQ(2, simulator.active.size());
          EXPECT_EQ(State::running, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          simulator.thread = 1;
          break;
        }
      case 2:
        {
          EXPECT_EQ(1, simulator.trace->pc(0));
          EXPECT_EQ(1, simulator.trace->pc(1));
          EXPECT_EQ(0, simulator.trace->sb_adr(0));
          EXPECT_EQ(0, simulator.trace->sb_adr(1));
          EXPECT_EQ(0, simulator.trace->sb_val(0));
          EXPECT_EQ(0, simulator.trace->sb_val(1));
          EXPECT_EQ(1, simulator.trace->sb_full(0));
          EXPECT_EQ(1, simulator.trace->sb_full(1));

          EXPECT_EQ(2, simulator.active.size());
          EXPECT_EQ(State::running, simulator.state[0]);
          EXPECT_EQ(State::running, simulator.state[1]);

          simulator.state[0] = State::flushing;
          simulator.thread = 0;
          break;
        }
      case 3:
        {
          simulator.state[1] = State::flushing;
          simulator.thread = 1;
          break;
        }
      default: FAIL() << "should have halted by now";
      }
  });

  ASSERT_EQ(trace->size(), simulator.step);

  ASSERT_EQ(State::running, simulator.state[0]);
  ASSERT_EQ(State::running, simulator.state[1]);

  // check Trace
  ASSERT_EQ(0, trace->exit);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}},
      {{0, 0}, {2, 1}}}),
    trace->pc_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}}}),
    trace->accu_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}}}),
    trace->mem_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}},
      {{0, 0}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    Trace::thread_map<bool>({
      {{0, false}, {1, true}, {3, false}},
      {{0, false}, {2, true}}}),
    trace->sb_full_updates);

  ASSERT_EQ(std::unordered_set<size_t>({2, 3}), trace->flushes);

  ASSERT_EQ(
    Trace::update_map<word_t>({{3, 0}}),
    trace->heap_adr_updates);
  ASSERT_EQ(
    Trace::heap_val_map({{0, {{3, 0}}}}),
    trace->heap_val_updates);
}

// Simulator::simulate =========================================================

TEST_F(Simulator, simulate_increment_check)
{
  std::ifstream trace_ifs("test/data/increment.check.t2.k16.trace");
  std::string expected((std::istreambuf_iterator<char>(trace_ifs)),
                        std::istreambuf_iterator<char>());

  trace =
    simulator.simulate(
      std::make_shared<Program::List>(
        create_from_file<Program>("test/data/increment.check.thread.0.asm"),
        create_from_file<Program>("test/data/increment.check.thread.n.asm")),
      {},
      16);

  ASSERT_EQ(
    Trace::update_map<word_t>({{3,0}, {14, 0}}),
    trace->heap_adr_updates);
  ASSERT_EQ(
    Trace::heap_val_map({{0, {{3, 0}, {14, 1}}}}),
    trace->heap_val_updates);

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(17, trace->size());
  ASSERT_EQ(expected, trace->print());
}

TEST_F(Simulator, simulate_increment_cas)
{
  std::ifstream trace_ifs("test/data/increment.cas.t2.k16.trace");
  std::string expected((std::istreambuf_iterator<char>(trace_ifs)),
                        std::istreambuf_iterator<char>());

  program = create_from_file<Program>("test/data/increment.cas.asm");

  trace =
    simulator.simulate(
      std::make_shared<Program::List>(program, program),
      {},
      16);

  ASSERT_EQ(
    Trace::update_map<word_t>({{3, 0}, {4, 0}, {12, 0}}),
    trace->heap_adr_updates);
  ASSERT_EQ(
    Trace::heap_val_map({{0, {{3, 0}, {12, 1}}}}),
    trace->heap_val_updates);

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(17, trace->size());
  ASSERT_EQ(expected, trace->print());
}

TEST_F(Simulator, simulate_indirect)
{
  std::ifstream trace_ifs("test/data/indirect.t1.trace");
  std::string expected((std::istreambuf_iterator<char>(trace_ifs)),
                        std::istreambuf_iterator<char>());

  trace =
    simulator.simulate(
      std::make_shared<Program::List>(
        create_from_file<Program>("test/data/indirect.asm")),
      {},
      8);

  ASSERT_EQ(
    Trace::update_map<word_t>({{2, 1}, {5, 0}}),
    trace->heap_adr_updates);
  ASSERT_EQ(
    Trace::heap_val_map({{0, {{5, 1}}}, {1, {{2, 0}}}}),
    trace->heap_val_updates);

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(9, trace->size());
  ASSERT_EQ(expected, trace->print());
}

TEST_F(Simulator, simulate_halt)
{
  std::ifstream trace_ifs("test/data/halt.t2.trace");
  std::string expected((std::istreambuf_iterator<char>(trace_ifs)),
                        std::istreambuf_iterator<char>());

  program = create_from_file<Program>("test/data/halt.asm");

  trace =
    simulator.simulate(
      std::make_shared<Program::List>(program, program),
      {},
      8);

  ASSERT_TRUE(trace->heap_adr_updates.empty());
  ASSERT_TRUE(trace->heap_val_updates.empty());

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(4, trace->size());
  ASSERT_EQ(expected, trace->print());
}

TEST_F(Simulator, simulate_load_uninitialized)
{
  auto programs = std::make_shared<Program::List>();

  for (word_t i = 1; i <= 3; i++)
    {
      std::istringstream code ("LOAD " + std::to_string(i));
      programs->push_back(Program(code, std::to_string(i) + ".asm"));
    }

  trace = simulator.simulate(programs, {}, 0);

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(6, trace->size());
  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 63883}},
      {{0, 0}, {2, 64750}},
      {{0, 0}, {5, 18152}}
    }),
    trace->accu_updates);
  ASSERT_EQ(
    MMap({
      {1, 63883},
      {2, 64750},
      {3, 18152},
    }),
    *trace->mmap);
}

TEST_F(Simulator, simulate_load_mmap)
{
  auto programs = std::make_shared<Program::List>();
  auto mmap =
    std::make_shared<MMap>(create_from_file<MMap>("test/data/init.mmap"));

  for (word_t i = 1; i <= 3; i++)
    {
      std::istringstream code ("LOAD " + std::to_string(i));
      programs->push_back(Program(code, std::to_string(i) + ".asm"));
    }

  trace = simulator.simulate(programs, mmap, 0);

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(6, trace->size());
  ASSERT_EQ(
    Trace::thread_map<word_t>({
      {{0, 0}, {1, 1}},
      {{0, 0}, {3, 2}},
      {{0, 0}, {2, 3}}
    }),
    trace->accu_updates);
  ASSERT_EQ(*mmap, *trace->mmap);
}

// Simulator::replay ===========================================================

TEST_F(Simulator, replay_increment_check)
{
  std::string trace_path = "test/data/increment.check.t2.k16.trace";

  std::ifstream sfs(trace_path);
  std::string expected((std::istreambuf_iterator<char>(sfs)),
                        std::istreambuf_iterator<char>());
  sfs.clear();
  sfs.seekg(0, std::ios::beg);

  trace = std::make_unique<Trace>(sfs, trace_path);

  trace = simulator.replay(*trace);

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(17, trace->size());
  ASSERT_EQ(expected, trace->print());
}

TEST_F(Simulator, replay_increment_cas)
{
  std::string trace_path = "test/data/increment.cas.t2.k16.trace";

  std::ifstream sfs(trace_path);
  std::string expected((std::istreambuf_iterator<char>(sfs)),
                        std::istreambuf_iterator<char>());
  sfs.clear();
  sfs.seekg(0, std::ios::beg);

  trace = std::make_unique<Trace>(sfs, trace_path);

  trace = simulator.replay(*trace);

  ASSERT_EQ(0, trace->exit);
  ASSERT_EQ(17, trace->size());
  ASSERT_EQ(expected, trace->print());
}

} // namespace ConcuBinE::test
