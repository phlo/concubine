#include <gtest/gtest.h>

#include "trace.hh"

#include "instruction.hh"
#include "parser.hh"

namespace test {

//==============================================================================
// Trace tests
//==============================================================================

struct Trace : public ::testing::Test
{
  std::string dummy_path = "dummy.trace";
  std::vector<std::string> check_program_paths = {
    "data/increment.check.thread.0.asm",
    "data/increment.check.thread.n.asm"
  };
  std::string cas_program_path = "data/increment.cas.asm";
  std::string check_trace_path = "data/increment.check.t2.k16.trace";
  std::string cas_trace_path = "data/increment.cas.t2.k16.trace";

  ::Trace::ptr trace;

  void create_dummy_trace (const size_t num_programs)
    {
      Program::List::ptr programs = std::make_unique<Program::List>();

      programs->resize(num_programs);

      trace = std::make_unique<::Trace>(programs);
    }
};

// Trace::Trace ================================================================

TEST_F(Trace, parse_check)
{
  trace =
    std::make_unique<::Trace>(create_from_file<::Trace>(check_trace_path));

  ASSERT_EQ(16, trace->bound);

  ASSERT_EQ(2, trace->programs->size());
  ASSERT_EQ(check_program_paths[0], trace->programs->at(0).path);
  ASSERT_EQ(check_program_paths[1], trace->programs->at(1).path);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0},
      {2,  1},
      {3,  0},
      {6,  1},
      {7,  0},
      {13, 1}}),
    trace->thread_updates);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0},
      {4,  1},
      {5,  2},
      {7,  3},
      {8,  4},
      {10, 5},
      {11, 6},
      {12, 1}}),
    trace->pc_updates[0]);
  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {2,  0},
      {6,  1},
      {13,  2},
      {14,  3},
      {15,  4}}),
    trace->pc_updates[1]);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0},
      {7, 1}}),
    trace->accu_updates[0]);
  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {2,  0},
      {13, 1},
      {14, 2}}),
    trace->accu_updates[1]);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0}}),
    trace->mem_updates[0]);
  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {2, 0}}),
    trace->mem_updates[1]);

  ASSERT_EQ(
    ::Trace::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    ::Trace::Thread_Updates<word_t>({
      {{1, 0}, {8, 1}},
      {{2, 0}, {15, 2}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    ::Trace::Thread_Updates<bool>({
      {{1, true}, {3, false}, {8, true}, {9, false}},
      {{2, false}, {15, true}, {16, false}}}),
    trace->sb_full_updates);

  ASSERT_EQ(::Trace::Flushes({3, 9, 16}), trace->flushes);

  ASSERT_EQ(
    ::Trace::Heap_Updates({{0, {{3, 0}, {9, 1}, {16, 2}}}}),
    trace->heap_updates);
}

TEST_F(Trace, parse_cas)
{
  trace = std::make_unique<::Trace>(create_from_file<::Trace>(cas_trace_path));

  ASSERT_EQ(16, trace->bound);

  ASSERT_EQ(2, trace->programs->size());
  ASSERT_EQ(cas_program_path, trace->programs->at(0).path);
  ASSERT_EQ(cas_program_path, trace->programs->at(1).path);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0},
      {2,  1},
      {4,  0},
      {5,  1},
      {6,  0},
      {8,  1},
      {10, 0},
      {14, 1}}),
    trace->thread_updates);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0},
      {6,  1},
      {7,  2},
      {10, 3},
      {11, 4},
      {12, 5},
      {13, 2}}),
    trace->pc_updates[0]);
  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {2,  0},
      {5,  1},
      {8,  2},
      {9,  3},
      {14, 4},
      {15, 5},
      {16, 2}}),
    trace->pc_updates[1]);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0},
      {10, 1}}),
    trace->accu_updates[0]);
  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {2,  0},
      {9,  1},
      {14, 0},
      {16, 1}}),
    trace->accu_updates[1]);

  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {1,  0},
      {13, 1}}),
    trace->mem_updates[0]);
  ASSERT_EQ(
    ::Trace::Updates<word_t>({
      {2, 0},
      {16, 1}}),
    trace->mem_updates[1]);

  ASSERT_EQ(
    ::Trace::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    ::Trace::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    ::Trace::Thread_Updates<bool>({
      {{1, true}, {4, false}},
      {{2, true}, {3, false}}}),
    trace->sb_full_updates);

  ASSERT_EQ(::Trace::Flushes({3, 4}), trace->flushes);

  ASSERT_EQ(
    ::Trace::Heap_Updates({{0, {{3, 0}, {11, 1}}}}),
    trace->heap_updates);
}

TEST_F(Trace, parse_empty_line)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n"
    "\n"
    "0\t0\tEXIT\t1\t0\t0\t0\t0\t0\t{}\n");

  trace = std::make_unique<::Trace>(inbuf, dummy_path);

  ASSERT_EQ(1, trace->size());
  ASSERT_EQ(1, trace->programs->size());
  ASSERT_EQ(cas_program_path, trace->programs->at(0).path);
}

TEST_F(Trace, parse_file_not_found)
{
  try
    {
      trace =
        std::make_unique<::Trace>(create_from_file<::Trace>("file_not_found"));
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_STREQ("file_not_found not found", e.what());
    }
}

TEST_F(Trace, parse_no_program)
{
  std::istringstream inbuf(
    ".\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: missing threads", e.what());
    }
}

TEST_F(Trace, parse_program_not_found)
{
  std::istringstream inbuf(
    dummy_path + "\n"
    ".\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: " + dummy_path + " not found", e.what());
    }
}

TEST_F(Trace, parse_missing_separator)
{
  std::istringstream inbuf(
    cas_program_path + "\n" +
    cas_program_path + "\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: 0 not found", e.what());
    }
}

TEST_F(Trace, parse_missing_trace)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: empty trace", e.what());
    }
}

TEST_F(Trace, parse_unknown_thread_id)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown thread id [1]", e.what());
    }
}

TEST_F(Trace, parse_illegal_thread_id)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n"
    "wrong\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal thread id [wrong]", e.what());
    }
}

TEST_F(Trace, parse_illegal_pc)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t1000\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal program counter [1000]", e.what());
    }
}

TEST_F(Trace, parse_unknown_label)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\tUNKNOWN\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown label [UNKNOWN]", e.what());
    }
}

TEST_F(Trace, parse_unknown_instruction)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tUNKNOWN\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown instruction [UNKNOWN]", e.what());
    }
}

TEST_F(Trace, parse_illegal_argument_label_not_supported)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\tILLEGAL\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: STORE does not support labels [ILLEGAL]",
        e.what());
    }
}

TEST_F(Trace, parse_illegal_argument_unknown_label)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t5\tJMP\tILLEGAL\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown label [ILLEGAL]", e.what());
    }
}

TEST_F(Trace, parse_illegal_accu)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\tILLEGAL\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal accumulator register value [ILLEGAL]",
        e.what());
    }
}

TEST_F(Trace, parse_illegal_mem)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\tILLEGAL\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal CAS memory register value [ILLEGAL]",
        e.what());
    }
}

TEST_F(Trace, parse_illegal_store_buffer_address)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\tILLEGAL\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal store buffer address [ILLEGAL]",
        e.what());
    }
}

TEST_F(Trace, parse_illegal_store_buffer_value)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\tILLEGAL\t0\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal store buffer value [ILLEGAL]",
        e.what());
    }
}

TEST_F(Trace, parse_illegal_store_buffer_full)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\tILLEGAL\t{}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal store buffer full flag [ILLEGAL]",
        e.what());
    }
}

TEST_F(Trace, parse_illegal_heap)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\tILLEGAL\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal heap update [ILLEGAL]", e.what());
    }

  // illegal set
  inbuf.str(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{ILLEGAL}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal heap update [{ILLEGAL}]", e.what());
    }

  // illegal index
  inbuf.str(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{(ILLEGAL,0)}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal heap update [{(ILLEGAL,0)}]",
        e.what());
    }

  // illegal value
  inbuf.str(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{(0,ILLEGAL)}\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal heap update [{(0,ILLEGAL)}]",
        e.what());
    }
}

TEST_F(Trace, parse_missing_pc)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing program counter", e.what());
    }
}

TEST_F(Trace, parse_missing_instruction_symbol)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing instruction symbol", e.what());
    }
}

TEST_F(Trace, parse_missing_instruction_argument)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing instruction argument", e.what());
    }
}

TEST_F(Trace, parse_missing_accu)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: missing accumulator register value",
        e.what());
    }
}

TEST_F(Trace, parse_missing_mem)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing CAS memory register value", e.what());
    }
}

TEST_F(Trace, parse_missing_store_buffer_address)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer address", e.what());
    }
}

TEST_F(Trace, parse_missing_store_buffer_value)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer value", e.what());
    }
}

TEST_F(Trace, parse_missing_store_buffer_full)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer full flag", e.what());
    }
}

TEST_F(Trace, parse_missing_heap)
{
  std::istringstream inbuf(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<::Trace>(inbuf, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing heap update", e.what());
    }
}

// Trace::push_back ============================================================

const std::vector<std::tuple<bound_t, word_t, word_t, word_t>> data {
  {1,  0, 0, 0},
  {2,  1, 0, 0},
  {3,  0, 0, 0},
  {4,  1, 0, 0},
  {5,  0, 1, 0},
  {6,  1, 1, 0},
  {7,  0, 1, 0},
  {8,  1, 1, 0},
  {9,  0, 0, 1},
  {10, 1, 0, 1},
  {11, 0, 0, 1},
  {12, 1, 0, 1},
  {13, 0, 1, 1},
  {14, 1, 1, 1},
  {15, 0, 1, 1},
  {16, 1, 1, 1},
};

// Trace::push_back_thread =====================================================

TEST_F(Trace, push_back_thread)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, _, __] : data)
    trace->push_back_thread(step, thread);

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(
    ::Trace::Updates<word_t> ({
      {1,  0},
      {2,  1},
      {3,  0},
      {4,  1},
      {5,  0},
      {6,  1},
      {7,  0},
      {8,  1},
      {9,  0},
      {10, 1},
      {11, 0},
      {12, 1},
      {13, 0},
      {14, 1},
      {15, 0},
      {16, 1}
    }),
    trace->thread_updates);
}

// Trace::push_back_pc =========================================================

const std::vector<::Trace::Updates<word_t>> push_back_expected {
  {{1, 0}, {5, 1}, {9, 0}, {13, 1}},
  {{2, 0}, {6, 1}, {10, 0}, {14, 1}}
};

TEST_F(Trace, push_back_pc)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, pc, _] : data)
    trace->push_back_pc(step, thread, pc);

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(push_back_expected, trace->pc_updates);
}

// Trace::push_back_accu =======================================================

TEST_F(Trace, push_back_accu)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, accu, _] : data)
    trace->push_back_accu(step, thread, accu);

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(push_back_expected, trace->accu_updates);
}

// Trace::push_back_mem ========================================================

TEST_F(Trace, push_back_mem)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, mem, _] : data)
    trace->push_back_mem(step, thread, mem);

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(push_back_expected, trace->mem_updates);
}

// Trace::push_back_sb_adr =====================================================

TEST_F(Trace, push_back_sb_adr)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, adr, _] : data)
    trace->push_back_sb_adr(step, thread, adr);

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(push_back_expected, trace->sb_adr_updates);
}

// Trace::push_back_sb_val =====================================================

TEST_F(Trace, push_back_sb_val)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, adr, _] : data)
    trace->push_back_sb_val(step, thread, adr);

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(push_back_expected, trace->sb_val_updates);
}

// Trace::push_back_sb_full ====================================================

TEST_F(Trace, push_back_sb_full)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, full, _] : data)
    trace->push_back_sb_full(step, thread, full);

  const std::vector<::Trace::Updates<bool>> expected {
    {{1, 0}, {5, 1}, {9, 0}, {13, 1}},
    {{2, 0}, {6, 1}, {10, 0}, {14, 1}}
  };

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(expected, trace->sb_full_updates);
}

// Trace::push_back_heap =======================================================

TEST_F(Trace, push_back_heap)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, idx, val] : data)
    trace->push_back_heap(step, {idx, val});

  ASSERT_EQ(data.size(), trace->bound);
  ASSERT_EQ(
    ::Trace::Heap_Updates ({
      {0, {{1, 0}, {9, 1}}},
      {1, {{5, 0}, {13, 1}}}
    }),
    trace->heap_updates);
}

// Trace::print ================================================================

TEST_F(Trace, print)
{
  trace = std::make_unique<::Trace>(create_from_file<::Trace>(cas_trace_path));

  std::ifstream ifs(cas_trace_path);
  std::string expected((std::istreambuf_iterator<char>(ifs)),
                        std::istreambuf_iterator<char>());

  ASSERT_EQ(expected, trace->print());
}

TEST_F(Trace, print_indirect_addressing)
{
  cas_trace_path = "data/indirect.addressing.trace";

  trace = std::make_unique<::Trace>(create_from_file<::Trace>(cas_trace_path));

  std::ifstream ifs(cas_trace_path);
  std::string expected((std::istreambuf_iterator<char>(ifs)),
                        std::istreambuf_iterator<char>());

  ASSERT_EQ(expected, trace->print());
}

// Trace::iterator =============================================================

TEST_F(Trace, iterator_check)
{
  trace =
    std::make_unique<::Trace>(
      create_from_file<::Trace>("data/increment.check.t2.k16.trace"));

  word_t tid[]      = {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1};
  word_t pc[]       = {0, 0, 0, 1, 2, 1, 3, 4, 4, 5, 6, 1, 2, 3, 4, 4};
  word_t accu[]     = {0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2};
  word_t mem[]      = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_adr[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_val[]   = {0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 2, 2};
  word_t sb_full[]  = {1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0};

  ::Trace::iterator it = trace->begin(), end = trace->end();

  for (size_t i = 0; it != end; i++, ++it)
    {
      ASSERT_EQ(tid[i], it->thread);
      ASSERT_EQ(pc[i], it->pc);
      ASSERT_EQ(accu[i], it->accu);
      ASSERT_EQ(mem[i], it->mem);
      ASSERT_EQ(sb_adr[i], it->sb_adr);
      ASSERT_EQ(sb_val[i], it->sb_val);
      ASSERT_EQ(sb_full[i], it->sb_full);

      if (i == 2)
        {
          ASSERT_EQ(0, it->heap->adr);
          ASSERT_EQ(0, it->heap->val);
        }
      else if (i == 8)
        {
          ASSERT_EQ(0, it->heap->adr);
          ASSERT_EQ(1, it->heap->val);
        }
      else if (i == 15)
        {
          ASSERT_EQ(0, it->heap->adr);
          ASSERT_EQ(2, it->heap->val);
        }
      else
        ASSERT_FALSE(it->heap);
    }

  // end() remains end()
  ASSERT_EQ(it++, end);
  ASSERT_EQ(++it, end);
}

TEST_F(Trace, iterator_cas)
{
  trace = std::make_unique<::Trace>(create_from_file<::Trace>(cas_trace_path));

  word_t tid[]      = {0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1};
  word_t pc[]       = {0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 2, 4, 5, 2};
  word_t accu[]     = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1};
  word_t mem[]      = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1};
  word_t sb_adr[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_val[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_full[]  = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

  ::Trace::iterator it = trace->begin(), end = trace->end();

  for (size_t i = 0; it != end; i++, ++it)
    {
      ASSERT_EQ(tid[i], it->thread);
      ASSERT_EQ(pc[i], it->pc);
      ASSERT_EQ(accu[i], it->accu);
      ASSERT_EQ(mem[i], it->mem);
      ASSERT_EQ(sb_adr[i], it->sb_adr);
      ASSERT_EQ(sb_val[i], it->sb_val);
      ASSERT_EQ(sb_full[i], it->sb_full);

      if (i == 2 || i == 3)
        {
          ASSERT_EQ(0, it->heap->adr);
          ASSERT_EQ(0, it->heap->val);
        }
      else if (i == 10 || i == 13)
        {
          ASSERT_EQ(0, it->heap->adr);
          ASSERT_EQ(1, it->heap->val);
        }
      else
        ASSERT_FALSE(it->heap);
    }

  // end() remains end()
  ASSERT_EQ(it++, end);
  ASSERT_EQ(++it, end);
}

// operator == =================================================================
// operator != =================================================================

TEST_F(Trace, operator_equals)
{
  Program::List::ptr p1 = std::make_unique<Program::List>(2);
  Program::List::ptr p2 = std::make_unique<Program::List>(2);

  p1->at(0).path = "program_1.asm";
  p1->at(0).push_back(Instruction::create("STORE", 1));
  p1->at(0).push_back(Instruction::create("ADDI", 1));

  p1->at(1).path = "program_2.asm";
  p1->at(1).push_back(Instruction::create("STORE", 1));
  p1->at(1).push_back(Instruction::create("ADDI", 1));

  p2->at(0).path = "program_1.asm";
  p2->at(0).push_back(Instruction::create("STORE", 1));
  p2->at(0).push_back(Instruction::create("ADDI", 1));

  p2->at(1).path = "program_2.asm";
  p2->at(1).push_back(Instruction::create("STORE", 1));
  p2->at(1).push_back(Instruction::create("ADDI", 1));

  ::Trace s1(p1);
  ::Trace s2(p2);

  // empty trace
  ASSERT_TRUE(s1 == s2);

  // non-empty trace
  s1.push_back(0, 0, 0, 0, 0, 0, false, {{1, 0}});
  s1.push_back(1, 0, 0, 0, 0, 0, false, {});
  s1.push_back(0, 1, 1, 0, 0, 0, false, {});
  s1.push_back(1, 1, 1, 0, 0, 0, false, {});
  s1.push_back(0, 2, 1, 0, 1, 1, true, {});
  s1.push_back(1, 2, 1, 0, 1, 1, true, {});

  s2.push_back(0, 0, 0, 0, 0, 0, false, {{1, 0}});
  s2.push_back(1, 0, 0, 0, 0, 0, false, {});
  s2.push_back(0, 1, 1, 0, 0, 0, false, {});
  s2.push_back(1, 1, 1, 0, 0, 0, false, {});
  s2.push_back(0, 2, 1, 0, 1, 1, true, {});
  s2.push_back(1, 2, 1, 0, 1, 1, true, {});

  ASSERT_TRUE(s1 == s2);

  // exit codes differ
  s2.exit = 1;

  ASSERT_TRUE(s1 != s2);

  s2.exit = 0;

  ASSERT_TRUE(s1 == s2);

  // traces differ
  ::Trace s3 = s2;

  s3.push_back(0, 2, 1, 0, 1, 1, false, {{1, 1}}); // flush

  ASSERT_TRUE(s1 != s3);

  // programs differ
  p2->at(1).push_back(Instruction::create("STORE", 1));

  ASSERT_TRUE(s1 != s2);

  p1->at(1).push_back(Instruction::create("STORE", 1));

  ASSERT_TRUE(s1 == s2);

  // list of programs differ
  p2->push_back(Program());

  ASSERT_TRUE(s1 != s2);

  p1->push_back(Program());

  ASSERT_TRUE(s1 == s2);

  // compare files
  ::Trace::ptr sp1 =
    std::make_unique<::Trace>(create_from_file<::Trace>(cas_trace_path));
  ::Trace::ptr sp2 =
    std::make_unique<::Trace>(create_from_file<::Trace>(cas_trace_path));

  ASSERT_TRUE(*sp1 == *sp2);
}

} // namespace test
