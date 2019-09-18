#include <gtest/gtest.h>

#include "trace.hh"

#include "instruction.hh"
#include "mmap.hh"
#include "parser.hh"

namespace ConcuBinE::test {

//==============================================================================
// Trace tests
//==============================================================================

struct Trace : public ::testing::Test
{
  template <class T>
  using update_map = ConcuBinE::Trace::update_map<T>;

  template <class T>
  using thread_map = ConcuBinE::Trace::thread_map<T>;

  using heap_val_map = ConcuBinE::Trace::heap_val_map;

  std::string dummy_path = "dummy.trace";
  std::vector<std::string> check_program_paths = {
    "test/data/increment.check.thread.0.asm",
    "test/data/increment.check.thread.n.asm"};
  std::string cas_program_path = "test/data/increment.cas.asm";
  std::string check_trace_path = "test/data/increment.check.t2.k16.trace";
  std::string cas_trace_path = "test/data/increment.cas.t2.k16.trace";

  std::unique_ptr<ConcuBinE::Trace> trace;

  void create_dummy_trace (const size_t num_programs)
    {
      auto programs = std::make_shared<Program::List>();
      programs->resize(num_programs);
      trace = std::make_unique<ConcuBinE::Trace>(programs);
    }
};

// Trace::Trace ================================================================

TEST_F(Trace, parse_check)
{
  trace =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(check_trace_path));

  ASSERT_EQ(17, trace->length);

  ASSERT_EQ(2, trace->programs->size());
  ASSERT_EQ(check_program_paths[0], trace->programs->at(0).path);
  ASSERT_EQ(check_program_paths[1], trace->programs->at(1).path);

  ASSERT_EQ(
    update_map<word_t>({
      {0,  0},
      {1,  1},
      {2,  0},
      {6,  1},
      {7,  0},
      {10, 1},
      {13, 0},
      {16, 1}}),
    trace->thread_updates);

  ASSERT_EQ(
    update_map<word_t>({
      {0,  0},
      {2,  1},
      {4,  2},
      {5,  3},
      {7,  4},
      {8,  5},
      {9,  6},
      {13, 7},
      {15, 1}}),
    trace->pc_updates[0]);
  ASSERT_EQ(
    update_map<word_t>({
      {1,  0},
      {6,  1},
      {10, 2},
      {11, 3},
      {12, 4},
      {16, 5}}),
    trace->pc_updates[1]);

  ASSERT_EQ(
    update_map<word_t>({
      {0, 0},
      {8, 1}}),
    trace->accu_updates[0]);
  ASSERT_EQ(
    update_map<word_t>({
      {1,  0},
      {12, 1}}),
    trace->accu_updates[1]);

  ASSERT_EQ(update_map<word_t>({{0, 0}}), trace->mem_updates[0]);
  ASSERT_EQ(update_map<word_t>({{1, 0}}), trace->mem_updates[1]);

  ASSERT_EQ(
    thread_map<word_t>({
      {{0, 0}},
      {{1, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    thread_map<word_t>({
      {{0, 0}, {9, 1}},
      {{1, 0}, {16, 1}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    thread_map<bool>({
      {{0, false}, {2, true}, {3, false}, {9, true}, {14, false}},
      {{1, false}, {16, true}}}),
    trace->sb_full_updates);

  ASSERT_EQ(std::unordered_set<size_t>({2, 13, 16}), trace->flushes);

  ASSERT_EQ(
    update_map<word_t>({
      {3, 0},
      {14, 0}}),
    trace->heap_adr_updates);
  ASSERT_EQ(
    heap_val_map({{0, {{3, 0}, {14, 1}}}}),
    trace->heap_val_updates);
}

TEST_F(Trace, parse_cas)
{
  trace =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(cas_trace_path));

  ASSERT_EQ(17, trace->length);

  ASSERT_EQ(2, trace->programs->size());
  ASSERT_EQ(cas_program_path, trace->programs->at(0).path);
  ASSERT_EQ(cas_program_path, trace->programs->at(1).path);

  ASSERT_EQ(
    update_map<word_t>({
      {0,  0},
      {1,  1},
      {3,  0},
      {4,  1},
      {5,  0},
      {7,  1},
      {8,  0},
      {9, 1},
      {13, 0}}),
    trace->thread_updates);

  ASSERT_EQ(
    update_map<word_t>({
      {0,  0},
      {3,  1},
      {6,  2},
      {8,  3},
      {13, 4},
      {14, 5},
      {15, 6},
      {16, 3}}),
    trace->pc_updates[0]);
  ASSERT_EQ(
    update_map<word_t>({
      {1,  0},
      {2,  1},
      {7,  2},
      {9,  3},
      {10, 4},
      {11, 5},
      {12, 6}}),
    trace->pc_updates[1]);

  ASSERT_EQ(
    update_map<word_t>({
      {0,  0},
      {14, 1},
      {15, 0}}),
    trace->accu_updates[0]);
  ASSERT_EQ(
    update_map<word_t>({
      {1,  0},
      {11, 1}}),
    trace->accu_updates[1]);

  ASSERT_EQ(
    update_map<word_t>({{0,  0}}),
    trace->mem_updates[0]);
  ASSERT_EQ(
    update_map<word_t>({{1, 0}}),
    trace->mem_updates[1]);

  ASSERT_EQ(
    thread_map<word_t>({
      {{0, 0}},
      {{1, 0}}}),
    trace->sb_adr_updates);

  ASSERT_EQ(
    thread_map<word_t>({
      {{0, 0}},
      {{1, 0}}}),
    trace->sb_val_updates);

  ASSERT_EQ(
    thread_map<bool>({
      {{0, false}, {3, true}, {5, false}},
      {{1, false}, {2, true}, {4, false}}}),
    trace->sb_full_updates);

  ASSERT_EQ(std::unordered_set<size_t>({2, 3}), trace->flushes);

  ASSERT_EQ(
    update_map<word_t>({{3, 0}, {4, 0}, {12, 0}}),
    trace->heap_adr_updates);
  ASSERT_EQ(
    heap_val_map({{0, {{3, 0}, {12, 1}}}}),
    trace->heap_val_updates);
}

TEST_F(Trace, parse_mmap)
{
  std::istringstream file (
    cas_program_path + "\n"
    ". test/data/init.mmap\n"
    "# tid\tpc\tcmd\targ\taccu\tmem\tadr\tval\tfull\theap\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\t# 0\n");

  trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);

  ASSERT_EQ(file.str(), trace->print());
  ASSERT_EQ(create_from_file<MMap>("test/data/init.mmap"), *trace->mmap);
}

TEST_F(Trace, parse_empty_line)
{
  std::istringstream file (
    check_program_paths[0] + "\n"
    ".\n"
    "\n"
    "0\t8\tEXIT\t1\t0\t0\t0\t0\t0\t{}\n");

  trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);

  ASSERT_EQ(1, trace->size());
  ASSERT_EQ(1, trace->programs->size());
  ASSERT_EQ(check_program_paths[0], trace->programs->at(0).path);
}

TEST_F(Trace, parse_file_not_found)
{
  try
    {
      trace =
        std::make_unique<ConcuBinE::Trace>(
          create_from_file<ConcuBinE::Trace>("file"));
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_STREQ("file not found", e.what());
    }
}

TEST_F(Trace, parse_no_program)
{
  std::istringstream file (
    ".\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: missing threads", e.what());
    }
}

TEST_F(Trace, parse_program_not_found)
{
  std::istringstream file (
    dummy_path + "\n"
    ".\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: " + dummy_path + " not found", e.what());
    }
}

TEST_F(Trace, parse_missing_separator)
{
  std::istringstream file (
    cas_program_path + "\n" +
    cas_program_path + "\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: 0 not found", e.what());
    }
}

TEST_F(Trace, parse_missing_trace)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: empty trace", e.what());
    }
}

TEST_F(Trace, parse_unknown_thread_id)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown thread id [1]", e.what());
    }
}

TEST_F(Trace, parse_illegal_thread_id)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n"
    "wrong\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal thread id [wrong]", e.what());
    }
}

TEST_F(Trace, parse_illegal_pc)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t1000\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal program counter [1000]", e.what());
    }
}

TEST_F(Trace, parse_unknown_label)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\tUNKNOWN\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown label [UNKNOWN]", e.what());
    }
}

TEST_F(Trace, parse_unknown_instruction)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tUNKNOWN\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown instruction [UNKNOWN]", e.what());
    }
}

TEST_F(Trace, parse_unexpected_instruction)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tCAS\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: unexpected instruction [CAS != STORE]",
        e.what());
    }
}

TEST_F(Trace, parse_illegal_argument_label_not_supported)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\tILLEGAL\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t6\tJMP\tILLEGAL\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown label [ILLEGAL]", e.what());
    }
}

TEST_F(Trace, parse_illegal_accu)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\tILLEGAL\t0\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\tILLEGAL\t0\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\tILLEGAL\t0\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\tILLEGAL\t0\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\tILLEGAL\t{}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\tILLEGAL\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal heap update [ILLEGAL]", e.what());
    }

  // illegal set
  file.str(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{ILLEGAL}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal heap update [{ILLEGAL}]", e.what());
    }

  // illegal index
  file.str(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{(ILLEGAL,0)}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal heap update [{(ILLEGAL,0)}]",
        e.what());
    }

  // illegal value
  file.str(
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{(0,ILLEGAL)}\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing program counter", e.what());
    }
}

TEST_F(Trace, parse_missing_instruction_symbol)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing instruction symbol", e.what());
    }
}

TEST_F(Trace, parse_missing_instruction_argument)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing instruction argument", e.what());
    }
}

TEST_F(Trace, parse_missing_accu)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
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
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing CAS memory register value", e.what());
    }
}

TEST_F(Trace, parse_missing_store_buffer_address)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer address", e.what());
    }
}

TEST_F(Trace, parse_missing_store_buffer_value)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer value", e.what());
    }
}

TEST_F(Trace, parse_missing_store_buffer_full)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer full flag", e.what());
    }
}

TEST_F(Trace, parse_missing_heap)
{
  std::istringstream file (
    cas_program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\n");

  try
    {
      trace = std::make_unique<ConcuBinE::Trace>(file, dummy_path);
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing heap update", e.what());
    }
}

// Trace::push_back ============================================================

const std::vector<std::tuple<size_t, word_t, word_t, word_t>> data {
  {0,  0, 0, 0},
  {1,  1, 0, 0},
  {2,  0, 0, 0},
  {3,  1, 0, 0},
  {4,  0, 1, 0},
  {5,  1, 1, 0},
  {6,  0, 1, 0},
  {7,  1, 1, 0},
  {8,  0, 0, 1},
  {9,  1, 0, 1},
  {10, 0, 0, 1},
  {11, 1, 0, 1},
  {12, 0, 1, 1},
  {13, 1, 1, 1},
  {14, 0, 1, 1},
  {15, 1, 1, 1},
};

template <class T, size_t i, size_t v>
const T updates = [] {
  T expected;

  constexpr bool is_vector =
    std::is_same<
      std::random_access_iterator_tag,
      typename T::iterator::iterator_category>::value;

  if constexpr(is_vector)
    expected.resize(2);

  for (const auto & tuple : data)
    {
      auto step = std::get<0>(tuple);
      auto val = std::get<v>(tuple);

      constexpr bool is_flat_map =
        std::is_literal_type<typename T::value_type>::value;

      if constexpr(is_flat_map)
        {
          if (expected.empty() || val != expected.rbegin()->second)
            expected.emplace_hint(expected.end(), step, val);
        }
      else
        {
          auto & updates = expected[std::get<i>(tuple)];
          if (updates.empty() || val != updates.rbegin()->second)
            updates.emplace_hint(updates.end(), step, val);
        }
    }

  return expected;
}();

// Trace::push_back_thread =====================================================

TEST_F(Trace, push_back_thread)
{
  create_dummy_trace(2);

  auto & expected = updates<update_map<word_t>, 1, 1>;

  for (const auto & [step, thread, _, __] : data)
    trace->push_back_thread(step, thread);

  ASSERT_EQ(data.size(), trace->length);
  ASSERT_EQ(data.size(), trace->thread_updates.size());
  ASSERT_EQ(expected, trace->thread_updates);
}

// Trace::push_back_pc =========================================================

TEST_F(Trace, push_back_pc)
{
  create_dummy_trace(2);

  auto & expected = updates<thread_map<word_t>, 1, 2>;

  for (const auto & [step, thread, pc, _] : data)
    trace->push_back_pc(step, thread, pc);

  ASSERT_EQ(4, trace->pc_updates[0].size());
  ASSERT_EQ(4, trace->pc_updates[1].size());
  ASSERT_EQ(expected, trace->pc_updates);
}

// Trace::push_back_accu =======================================================

TEST_F(Trace, push_back_accu)
{
  create_dummy_trace(2);

  auto & expected = updates<thread_map<word_t>, 1, 2>;

  for (const auto & [step, thread, accu, _] : data)
    trace->push_back_accu(step, thread, accu);

  ASSERT_EQ(4, trace->accu_updates[0].size());
  ASSERT_EQ(4, trace->accu_updates[1].size());
  ASSERT_EQ(expected, trace->accu_updates);
}

// Trace::push_back_mem ========================================================

TEST_F(Trace, push_back_mem)
{
  create_dummy_trace(2);

  auto & expected = updates<thread_map<word_t>, 1, 2>;

  for (const auto & [step, thread, mem, _] : data)
    trace->push_back_mem(step, thread, mem);

  ASSERT_EQ(4, trace->mem_updates[0].size());
  ASSERT_EQ(4, trace->mem_updates[1].size());
  ASSERT_EQ(expected, trace->mem_updates);
}

// Trace::push_back_sb_adr =====================================================

TEST_F(Trace, push_back_sb_adr)
{
  create_dummy_trace(2);

  auto & expected = updates<thread_map<word_t>, 1, 2>;

  for (const auto & [step, thread, adr, _] : data)
    trace->push_back_sb_adr(step, thread, adr);

  ASSERT_EQ(4, trace->sb_adr_updates[0].size());
  ASSERT_EQ(4, trace->sb_adr_updates[1].size());
  ASSERT_EQ(expected, trace->sb_adr_updates);
}

// Trace::push_back_sb_val =====================================================

TEST_F(Trace, push_back_sb_val)
{
  create_dummy_trace(2);

  auto & expected = updates<thread_map<word_t>, 1, 2>;

  for (const auto & [step, thread, adr, _] : data)
    trace->push_back_sb_val(step, thread, adr);

  ASSERT_EQ(4, trace->sb_val_updates[0].size());
  ASSERT_EQ(4, trace->sb_val_updates[1].size());
  ASSERT_EQ(expected, trace->sb_val_updates);
}

// Trace::push_back_sb_full ====================================================

TEST_F(Trace, push_back_sb_full)
{
  create_dummy_trace(2);

  auto & expected = updates<thread_map<bool>, 1, 2>;

  for (const auto & [step, thread, full, _] : data)
    trace->push_back_sb_full(step, thread, full);

  ASSERT_EQ(4, trace->sb_full_updates[0].size());
  ASSERT_EQ(4, trace->sb_full_updates[1].size());
  ASSERT_EQ(expected, trace->sb_full_updates);
}

// Trace::push_back_heap =======================================================

TEST_F(Trace, push_back_heap)
{
  create_dummy_trace(2);

  update_map<word_t> expected_adr;
  auto & expected_val = updates<heap_val_map, 2, 3>;

  for (const auto & [step, thread, idx, val] : data)
    {
      expected_adr.emplace_hint(expected_adr.end(), step, idx);
      trace->push_back_heap(step, idx, val);
    }

  ASSERT_EQ(data.size(), trace->size());
  ASSERT_EQ(data.size(), trace->heap_adr_updates.size());
  ASSERT_EQ(expected_adr, trace->heap_adr_updates);
  ASSERT_EQ(2, trace->heap_val_updates[0].size());
  ASSERT_EQ(2, trace->heap_val_updates[1].size());
  ASSERT_EQ(expected_val, trace->heap_val_updates);
}

// Trace::thread ===============================================================

TEST_F(Trace, thread)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, _, __] : data)
    {
      trace->push_back_thread(step, thread);
      ASSERT_EQ(thread, trace->thread());
    }
}

TEST_F(Trace, thread_k)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, _, __] : data)
    trace->push_back_thread(step, thread);

  for (const auto & [step, thread, _, __] : data)
    ASSERT_EQ(thread, trace->thread(step));
}

// Trace::pc ===================================================================

TEST_F(Trace, pc)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, pc, _] : data)
    {
      trace->push_back_pc(step, thread, pc);
      ASSERT_EQ(pc, trace->pc(thread));
    }
}

TEST_F(Trace, pc_k)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, pc, _] : data)
    {
      trace->push_back_thread(step, thread);
      trace->push_back_pc(step, thread, pc);
    }

  for (const auto & [step, thread, pc, _] : data)
    ASSERT_EQ(pc, trace->pc(step, thread));
}

// Trace::accu =================================================================

TEST_F(Trace, accu)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, accu, _] : data)
    {
      trace->push_back_accu(step, thread, accu);
      ASSERT_EQ(accu, trace->accu(thread));
    }
}

TEST_F(Trace, accu_k)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, accu, _] : data)
    {
      trace->push_back_thread(step, thread);
      trace->push_back_accu(step, thread, accu);
    }

  for (const auto & [step, thread, accu, _] : data)
    ASSERT_EQ(accu, trace->accu(step, thread));
}

// Trace::mem ==================================================================

TEST_F(Trace, mem)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, mem, _] : data)
    {
      trace->push_back_mem(step, thread, mem);
      ASSERT_EQ(mem, trace->mem(thread));
    }
}

TEST_F(Trace, mem_k)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, mem, _] : data)
    {
      trace->push_back_thread(step, thread);
      trace->push_back_mem(step, thread, mem);
    }

  for (const auto & [step, thread, mem, _] : data)
    ASSERT_EQ(mem, trace->mem(step, thread));
}

// Trace::sb_adr ===============================================================

TEST_F(Trace, sb_adr)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, sb_adr, _] : data)
    {
      trace->push_back_sb_adr(step, thread, sb_adr);
      ASSERT_EQ(sb_adr, trace->sb_adr(thread));
    }
}

TEST_F(Trace, sb_adr_k)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, sb_adr, _] : data)
    {
      trace->push_back_thread(step, thread);
      trace->push_back_sb_adr(step, thread, sb_adr);
    }

  for (const auto & [step, thread, sb_adr, _] : data)
    ASSERT_EQ(sb_adr, trace->sb_adr(step, thread));
}

// Trace::sb_val ===============================================================

TEST_F(Trace, sb_val)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, sb_val, _] : data)
    {
      trace->push_back_sb_val(step, thread, sb_val);
      ASSERT_EQ(sb_val, trace->sb_val(thread));
    }
}

TEST_F(Trace, sb_val_k)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, sb_val, _] : data)
    {
      trace->push_back_thread(step, thread);
      trace->push_back_sb_val(step, thread, sb_val);
    }

  for (const auto & [step, thread, sb_val, _] : data)
    ASSERT_EQ(sb_val, trace->sb_val(step, thread));
}

// Trace::sb_full ==============================================================

TEST_F(Trace, sb_full)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, sb_full, _] : data)
    {
      trace->push_back_sb_full(step, thread, sb_full);
      ASSERT_EQ(sb_full, trace->sb_full(thread));
    }
}

TEST_F(Trace, sb_full_k)
{
  create_dummy_trace(2);

  for (const auto & [step, thread, sb_full, _] : data)
    {
      trace->push_back_thread(step, thread);
      trace->push_back_sb_full(step, thread, sb_full);
    }

  for (const auto & [step, thread, sb_full, _] : data)
    ASSERT_EQ(sb_full, trace->sb_full(step, thread));
}

// Trace::heap =================================================================

TEST_F(Trace, heap)
{
  create_dummy_trace(2);

  for (const auto & [step, _, adr, val] : data)
    {
      trace->push_back_heap(step, adr, val);
      ASSERT_EQ(val, trace->heap(adr));
    }
}

TEST_F(Trace, heap_k)
{
  create_dummy_trace(2);

  for (const auto & [step, _, adr, val] : data)
    trace->push_back_heap(step, adr, val);

  for (const auto & [step, _, adr, val] : data)
    ASSERT_EQ(val, trace->heap(step, adr));
}

// Trace::print ================================================================

TEST_F(Trace, print)
{
  trace =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(cas_trace_path));

  std::ifstream ifs(cas_trace_path);
  std::string expected((std::istreambuf_iterator<char>(ifs)),
                        std::istreambuf_iterator<char>());

  ASSERT_EQ(17, trace->length);
  ASSERT_EQ(expected, trace->print());
}

TEST_F(Trace, print_indirect_addressing)
{
  cas_trace_path = "test/data/indirect.addressing.trace";

  trace =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(cas_trace_path));

  std::ifstream ifs(cas_trace_path);
  std::string expected((std::istreambuf_iterator<char>(ifs)),
                        std::istreambuf_iterator<char>());

  ASSERT_EQ(expected, trace->print());
}

// Trace::iterator =============================================================

TEST_F(Trace, iterator_check)
{
  trace =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(
        "test/data/increment.check.t2.k16.trace"));

                    // 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16
  word_t tid[]      = {0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 1};
  word_t pc[]       = {0, 0, 1, 1, 2, 3, 1, 4, 5, 6, 2, 3, 4, 7, 7, 1, 5};
  word_t accu[]     = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1};
  word_t mem[]      = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_adr[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_val[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1};
  word_t sb_full[]  = {0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1};

  ConcuBinE::Trace::iterator it = trace->begin(), end = trace->end();

  for (size_t i = 0; it != end; i++, ++it)
    {
      ASSERT_EQ(tid[i], it->thread);
      ASSERT_EQ(pc[i], it->pc);
      ASSERT_EQ(accu[i], it->accu);
      ASSERT_EQ(mem[i], it->mem);
      ASSERT_EQ(sb_adr[i], it->sb_adr);
      ASSERT_EQ(sb_val[i], it->sb_val);
      ASSERT_EQ(sb_full[i], it->sb_full);

      if (i == 3)
        {
          ASSERT_EQ(0, it->heap->first);
          ASSERT_EQ(0, it->heap->second);
        }
      else if (i == 14)
        {
          ASSERT_EQ(0, it->heap->first);
          ASSERT_EQ(1, it->heap->second);
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
  trace =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(cas_trace_path));

                    // 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16
  word_t tid[]      = {0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0};
  word_t pc[]       = {0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 4, 5, 6, 3};
  word_t accu[]     = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0};
  word_t mem[]      = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_adr[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_val[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_full[]  = {0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

  ConcuBinE::Trace::iterator it = trace->begin(), end = trace->end();

  for (size_t i = 0; it != end; i++, ++it)
    {
      ASSERT_EQ(tid[i], it->thread);
      ASSERT_EQ(pc[i], it->pc);
      ASSERT_EQ(accu[i], it->accu);
      ASSERT_EQ(mem[i], it->mem);
      ASSERT_EQ(sb_adr[i], it->sb_adr);
      ASSERT_EQ(sb_val[i], it->sb_val);
      ASSERT_EQ(sb_full[i], it->sb_full);

      if (i == 3 || i == 4)
        {
          ASSERT_EQ(0, it->heap->first);
          ASSERT_EQ(0, it->heap->second);
        }
      else if (i == 12)
        {
          ASSERT_EQ(0, it->heap->first);
          ASSERT_EQ(1, it->heap->second);
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
  auto p1 = std::make_shared<Program::List>(2);
  auto p2 = std::make_shared<Program::List>(2);

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

  ConcuBinE::Trace s1(p1);
  ConcuBinE::Trace s2(p2);

  // empty trace
  ASSERT_TRUE(s1 == s2);

  // non-empty trace
  std::optional<std::pair<word_t, word_t>> heap;
  s1.push_back(0, 0, 0, 0, 0, 0, false, heap = {1, 0});
  s1.push_back(1, 0, 0, 0, 0, 0, false, heap);
  s1.push_back(0, 1, 1, 0, 0, 0, false, heap);
  s1.push_back(1, 1, 1, 0, 0, 0, false, heap);
  s1.push_back(0, 2, 1, 0, 1, 1, true, heap);
  s1.push_back(1, 2, 1, 0, 1, 1, true, heap);

  s2.push_back(0, 0, 0, 0, 0, 0, false, heap = {1, 0});
  s2.push_back(1, 0, 0, 0, 0, 0, false, heap);
  s2.push_back(0, 1, 1, 0, 0, 0, false, heap);
  s2.push_back(1, 1, 1, 0, 0, 0, false, heap);
  s2.push_back(0, 2, 1, 0, 1, 1, true, heap);
  s2.push_back(1, 2, 1, 0, 1, 1, true, heap);

  ASSERT_TRUE(s1 == s2);

  // exit codes differ
  s2.exit = 1;

  ASSERT_TRUE(s1 != s2);

  s2.exit = 0;

  ASSERT_TRUE(s1 == s2);

  // traces differ
  ConcuBinE::Trace s3 = s2;

  s3.push_back(0, 2, 1, 0, 1, 1, false, heap = {1, 1}); // flush

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
  auto sp1 =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(cas_trace_path));
  auto sp2 =
    std::make_unique<ConcuBinE::Trace>(
      create_from_file<ConcuBinE::Trace>(cas_trace_path));

  ASSERT_TRUE(*sp1 == *sp2);
}

} // namespace ConcuBinE::test
