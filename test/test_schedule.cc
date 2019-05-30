#include <gtest/gtest.h>

#include "schedule.hh"

#include "instructionset.hh"
#include "parser.hh"

using namespace std;

struct ScheduleTest : public ::testing::Test
{
  string dummy_path = "dummy.schedule";
  string program_path = "data/increment.cas.asm";
  string schedule_path = "data/increment.cas.t2.k16.schedule";

  Schedule_ptr schedule;

  void create_dummy_schedule (const size_t num_programs)
    {
      Program_list_ptr programs = make_shared<Program_list>();

      for (size_t i = 0; i < num_programs; i++)
        programs->push_back(make_shared<Program>());

      schedule = make_shared<Schedule>(programs);
    }
};

/* Schedule::Schedule *********************************************************/
TEST_F(ScheduleTest, parse_check)
{
  schedule = create_from_file<Schedule>("data/increment.check.t2.k16.schedule");

  ASSERT_EQ(16, schedule->bound);

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(
    "data/increment.check.thread.0.asm",
    schedule->programs->at(0)->path);
  ASSERT_EQ(
    "data/increment.check.thread.n.asm",
    schedule->programs->at(1)->path);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0},
      {2,  1},
      {3,  0},
      {6,  1},
      {7,  0},
      {13, 1}}),
    schedule->thread_updates);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0},
      {4,  1},
      {5,  2},
      {7,  3},
      {8,  4},
      {10, 5},
      {11, 6},
      {12, 1}}),
    schedule->pc_updates[0]);
  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {2,  0},
      {6,  1},
      {13,  2},
      {14,  3},
      {15,  4}}),
    schedule->pc_updates[1]);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0},
      {7, 1}}),
    schedule->accu_updates[0]);
  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {2,  0},
      {13, 1},
      {14, 2}}),
    schedule->accu_updates[1]);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0}}),
    schedule->mem_updates[0]);
  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {2, 0}}),
    schedule->mem_updates[1]);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}}}),
    schedule->sb_adr_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}, {8, 1}},
      {{2, 0}, {15, 2}}}),
    schedule->sb_val_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<bool>({
      {{1, true}, {3, false}, {8, true}, {9, false}},
      {{2, false}, {15, true}, {16, false}}}),
    schedule->sb_full_updates);

  ASSERT_EQ(Schedule::Flushes({3, 9, 16}), schedule->flushes);

  ASSERT_EQ(
    Schedule::Heap_Updates({{0, {{3, 0}, {9, 1}, {16, 2}}}}),
    schedule->heap_updates);
}

TEST_F(ScheduleTest, parse_cas)
{
  schedule_path = "data/increment.cas.t2.k16.schedule";

  schedule = create_from_file<Schedule>(schedule_path);

  ASSERT_EQ(16, schedule->bound);

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(program_path, schedule->programs->at(0)->path);
  ASSERT_EQ(program_path, schedule->programs->at(1)->path);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0},
      {2,  1},
      {4,  0},
      {5,  1},
      {6,  0},
      {8,  1},
      {10, 0},
      {14, 1}}),
    schedule->thread_updates);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0},
      {6,  1},
      {7,  2},
      {10, 3},
      {11, 4},
      {12, 5},
      {13, 2}}),
    schedule->pc_updates[0]);
  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {2,  0},
      {5,  1},
      {8,  2},
      {9,  3},
      {14, 4},
      {15, 5},
      {16, 2}}),
    schedule->pc_updates[1]);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0},
      {10, 1}}),
    schedule->accu_updates[0]);
  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {2,  0},
      {9,  1},
      {14, 0},
      {16, 1}}),
    schedule->accu_updates[1]);

  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {1,  0},
      {13, 1}}),
    schedule->mem_updates[0]);
  ASSERT_EQ(
    Schedule::Updates<word_t>({
      {2, 0},
      {16, 1}}),
    schedule->mem_updates[1]);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}}}),
    schedule->sb_adr_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<word_t>({
      {{1, 0}},
      {{2, 0}}}),
    schedule->sb_val_updates);

  ASSERT_EQ(
    Schedule::Thread_Updates<bool>({
      {{1, true}, {4, false}},
      {{2, true}, {3, false}}}),
    schedule->sb_full_updates);

  ASSERT_EQ(Schedule::Flushes({3, 4}), schedule->flushes);

  ASSERT_EQ(
    Schedule::Heap_Updates({{0, {{3, 0}, {11, 1}}}}),
    schedule->heap_updates);
}

TEST_F(ScheduleTest, parse_empty_line)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n"
    "\n"
    "0\t0\tEXIT\t1\t0\t0\t0\t0\t0\t{}\n");

  schedule = make_shared<Schedule>(inbuf, dummy_path);

  ASSERT_EQ(1, schedule->size());
  ASSERT_EQ(1, schedule->programs->size());
  ASSERT_EQ(program_path, schedule->programs->at(0)->path);
}

TEST_F(ScheduleTest, parse_file_not_found)
{
  try
    {
      schedule = create_from_file<Schedule>("file_not_found");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("file_not_found not found", e.what());
    }
}

TEST_F(ScheduleTest, parse_no_program)
{
  istringstream inbuf(
    ".\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: missing threads", e.what());
    }
}

TEST_F(ScheduleTest, parse_program_not_found)
{
  istringstream inbuf(
    dummy_path + "\n"
    ".\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: " + dummy_path + " not found", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_separator)
{
  istringstream inbuf(
    program_path + "\n" +
    program_path + "\n"
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: 0 not found", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_trace)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: empty schedule", e.what());
    }
}

TEST_F(ScheduleTest, parse_unknown_thread_id)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n"
    "1\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown thread id [1]", e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_thread_id)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n"
    "wrong\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal thread id [wrong]", e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_pc)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t1000\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal program counter [1000]", e.what());
    }
}

TEST_F(ScheduleTest, parse_unknown_label)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\tUNKNOWN\tSTORE\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown label [UNKNOWN]", e.what());
    }
}

TEST_F(ScheduleTest, parse_unknown_instruction)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tUNKNOWN\t0\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown instruction [UNKNOWN]", e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_argument_label_not_supported)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\tILLEGAL\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: STORE does not support labels [ILLEGAL]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_argument_unknown_label)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t5\tJMP\tILLEGAL\t0\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: unknown label [ILLEGAL]", e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_accu)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\tILLEGAL\t0\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal accumulator register value [ILLEGAL]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_mem)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\tILLEGAL\t0\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal CAS memory register value [ILLEGAL]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_store_buffer_address)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\tILLEGAL\t0\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal store buffer address [ILLEGAL]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_store_buffer_value)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\tILLEGAL\t0\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal store buffer value [ILLEGAL]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_store_buffer_full)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\tILLEGAL\t{}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal store buffer full flag [ILLEGAL]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_heap)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\tILLEGAL\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal heap update [ILLEGAL]", e.what());
    }

  /* illegal set */
  inbuf.str(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{ILLEGAL}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: illegal heap update [{ILLEGAL}]", e.what());
    }

  /* illegal index */
  inbuf.str(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{(ILLEGAL,0)}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal heap update [{(ILLEGAL,0)}]",
        e.what());
    }

  /* illegal value */
  inbuf.str(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\t{(0,ILLEGAL)}\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal heap update [{(0,ILLEGAL)}]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_pc)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing program counter", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_instruction_symbol)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing instruction symbol", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_instruction_argument)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing instruction argument", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_accu)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: missing accumulator register value",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_mem)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing CAS memory register value", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_store_buffer_address)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer address", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_store_buffer_value)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer value", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_store_buffer_full)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing store buffer full flag", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_heap)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\t0\t0\t0\n");

  try
    {
      schedule = make_shared<Schedule>(inbuf, dummy_path);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing heap update", e.what());
    }
}

/* Schedule::push_back ********************************************************/
using Insert_Data = tuple<bound_t, word_t, word_t, word_t>;

const vector<Insert_Data> insert_data {
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

/* Schedule::insert_thread ****************************************************/
TEST_F(ScheduleTest, insert_thread)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, _, __] : insert_data)
    schedule->insert_thread(step, thread);

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(
    Schedule::Updates<word_t> ({
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
    schedule->thread_updates);
}

/* Schedule::insert_pc ********************************************************/
const vector<Schedule::Updates<word_t>> insert_expected {
  {{1, 0}, {5, 1}, {9, 0}, {13, 1}},
  {{2, 0}, {6, 1}, {10, 0}, {14, 1}}
};

TEST_F(ScheduleTest, insert_pc)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, pc, _] : insert_data)
    schedule->insert_pc(step, thread, pc);

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(insert_expected, schedule->pc_updates);
}

/* Schedule::insert_accu ******************************************************/
TEST_F(ScheduleTest, insert_accu)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, accu, _] : insert_data)
    schedule->insert_accu(step, thread, accu);

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(insert_expected, schedule->accu_updates);
}

/* Schedule::insert_mem *******************************************************/
TEST_F(ScheduleTest, insert_mem)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, mem, _] : insert_data)
    schedule->insert_mem(step, thread, mem);

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(insert_expected, schedule->mem_updates);
}

/* Schedule::insert_sb_adr ****************************************************/
TEST_F(ScheduleTest, insert_sb_adr)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, adr, _] : insert_data)
    schedule->insert_sb_adr(step, thread, adr);

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(insert_expected, schedule->sb_adr_updates);
}

/* Schedule::insert_sb_val ****************************************************/
TEST_F(ScheduleTest, insert_sb_val)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, adr, _] : insert_data)
    schedule->insert_sb_val(step, thread, adr);

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(insert_expected, schedule->sb_val_updates);
}

/* Schedule::insert_sb_full ***************************************************/
TEST_F(ScheduleTest, insert_sb_full)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, full, _] : insert_data)
    schedule->insert_sb_full(step, thread, full);

  const vector<Schedule::Updates<bool>> expected {
    {{1, 0}, {5, 1}, {9, 0}, {13, 1}},
    {{2, 0}, {6, 1}, {10, 0}, {14, 1}}
  };

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(expected, schedule->sb_full_updates);
}

/* Schedule::insert_heap ******************************************************/
TEST_F(ScheduleTest, insert_heap)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, idx, val] : insert_data)
    schedule->insert_heap(step, {idx, val});

  ASSERT_EQ(insert_data.size(), schedule->bound);
  ASSERT_EQ(
    Schedule::Heap_Updates ({
      {0, {{1, 0}, {9, 1}}},
      {1, {{5, 0}, {13, 1}}}
    }),
    schedule->heap_updates);
}

/* Schedule::print ************************************************************/
TEST_F(ScheduleTest, print)
{
  schedule = create_from_file<Schedule>(schedule_path);

  ifstream ifs(schedule_path);
  string expected(
    (istreambuf_iterator<char>(ifs)),
    istreambuf_iterator<char>());

  ASSERT_EQ(expected, schedule->print());
}

TEST_F(ScheduleTest, print_indirect_addressing)
{
  schedule_path = "data/indirect.addressing.schedule";

  schedule = create_from_file<Schedule>(schedule_path);

  ifstream ifs(schedule_path);
  string expected(
    (istreambuf_iterator<char>(ifs)),
    istreambuf_iterator<char>());

  ASSERT_EQ(expected, schedule->print());
}

/* Schedule::iterator *********************************************************/
TEST_F(ScheduleTest, iterator_check)
{
  schedule = create_from_file<Schedule>("data/increment.check.t2.k16.schedule");

  word_t tid[]      = {0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1};
  word_t pc[]       = {0, 0, 0, 1, 2, 1, 3, 4, 4, 5, 6, 1, 2, 3, 4, 4};
  word_t accu[]     = {0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2};
  word_t mem[]      = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_adr[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_val[]   = {0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 2, 2};
  word_t sb_full[]  = {1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0};

  Schedule::iterator it = schedule->begin(), end = schedule->end();

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

  /* end() remains end() */
  ASSERT_EQ(it++, end);
  ASSERT_EQ(++it, end);
}

TEST_F(ScheduleTest, iterator_cas)
{
  schedule = create_from_file<Schedule>(schedule_path);

  word_t tid[]      = {0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1};
  word_t pc[]       = {0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 2, 4, 5, 2};
  word_t accu[]     = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1};
  word_t mem[]      = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1};
  word_t sb_adr[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_val[]   = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
  word_t sb_full[]  = {1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

  Schedule::iterator it = schedule->begin(), end = schedule->end();

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

  /* end() remains end() */
  ASSERT_EQ(it++, end);
  ASSERT_EQ(++it, end);
}

/* operator == ****************************************************************/
/* operator != ****************************************************************/
TEST_F(ScheduleTest, operator_equals)
{
  Program_list_ptr p1 = make_shared<Program_list>();
  Program_list_ptr p2 = make_shared<Program_list>();

  p1->push_back(make_shared<Program>());
  p1->push_back(make_shared<Program>());

  p2->push_back(make_shared<Program>());
  p2->push_back(make_shared<Program>());

  p1->at(0)->path = "program_1.asm";
  p1->at(0)->push_back(Instruction::Set::create("STORE", 1));
  p1->at(0)->push_back(Instruction::Set::create("ADDI", 1));

  p1->at(1)->path = "program_2.asm";
  p1->at(1)->push_back(Instruction::Set::create("STORE", 1));
  p1->at(1)->push_back(Instruction::Set::create("ADDI", 1));

  p2->at(0)->path = "program_1.asm";
  p2->at(0)->push_back(Instruction::Set::create("STORE", 1));
  p2->at(0)->push_back(Instruction::Set::create("ADDI", 1));

  p2->at(1)->path = "program_2.asm";
  p2->at(1)->push_back(Instruction::Set::create("STORE", 1));
  p2->at(1)->push_back(Instruction::Set::create("ADDI", 1));

  Schedule s1(p1);
  Schedule s2(p2);

  /* empty schedule */
  ASSERT_TRUE(s1 == s2);

  /* non-empty schedule */
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

  /* exit codes differ */
  s2.exit = 1;

  ASSERT_TRUE(s1 != s2);

  s2.exit = 0;

  ASSERT_TRUE(s1 == s2);

  /* traces differ */
  Schedule s3 = s2;

  s3.push_back(0, 2, 1, 0, 1, 1, false, {{1, 1}}); // flush

  ASSERT_TRUE(s1 != s3);

  /* programs differ */
  p2->at(1)->push_back(Instruction::Set::create("STORE", 1));

  ASSERT_TRUE(s1 != s2);

  p1->at(1)->push_back(Instruction::Set::create("STORE", 1));

  ASSERT_TRUE(s1 == s2);

  /* list of programs differ */
  p2->push_back(make_shared<Program>());

  ASSERT_TRUE(s1 != s2);

  p1->push_back(make_shared<Program>());

  ASSERT_TRUE(s1 == s2);

  /* compare files */
  Schedule_ptr sp1 = create_from_file<Schedule>(schedule_path);
  Schedule_ptr sp2 = create_from_file<Schedule>(schedule_path);

  ASSERT_TRUE(*sp1 == *sp2);
}
