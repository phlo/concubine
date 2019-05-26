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

  SchedulePtr schedule;

  void create_dummy_schedule (const size_t num_programs)
    {
      ProgramListPtr programs = make_shared<ProgramList>();

      for (size_t i = 0; i < num_programs; i++)
        programs->push_back(make_shared<Program>());

      schedule = make_shared<Schedule>(programs);
    }
};

// Schedule::Schedule(istream & file, string & name)
TEST_F(ScheduleTest, parse)
{
  schedule = create_from_file<Schedule>(schedule_path);

  ASSERT_EQ(16, schedule->bound);

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(program_path, schedule->programs->at(0)->path);
  ASSERT_EQ(program_path, schedule->programs->at(1)->path);

  ASSERT_EQ(
    // vector<word>({0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1}),
    Schedule::Update_Map({
      {1,  0},
      {2,  1},
      {4,  0},
      {7,  1},
      {8,  0},
      {10, 1},
      {12, 0},
      {16, 1}}),
    schedule->thread_updates);

  ASSERT_EQ(
    Schedule::Update_Map({
      {1,  0},
      {4,  1},
      {5,  2},
      {6,  3},
      {8,  4},
      {9,  5},
      {12, 2},
      {13, 3},
      {14, 4},
      {15, 5}}),
    schedule->pc_updates[0]);
  ASSERT_EQ(
    Schedule::Update_Map({
      {2,  0},
      {3,  1},
      {7,  2},
      {10, 3},
      {11, 4},
      {16, 5}}),
    schedule->pc_updates[1]);

  ASSERT_EQ(
    Schedule::Update_Map({
      {1,  0},
      {6,  1},
      {13, 2},
      {14, 1}}),
    schedule->accu_updates[0]);
  ASSERT_EQ(
    Schedule::Update_Map({
      {2,  0},
      {10, 1},
      {11, 0}}),
    schedule->accu_updates[1]);

  ASSERT_EQ(
    Schedule::Update_Map({
      {1,  0},
      {12, 1}}),
    schedule->mem_updates[0]);
  ASSERT_EQ(
    Schedule::Update_Map({
      {2, 0}}),
    schedule->mem_updates[1]);

  ASSERT_EQ(
    Schedule::Heap_Updates({{0, {{1, 0}, {8, 1}, {14, 2}}}}),
    schedule->heap_updates);
}

TEST_F(ScheduleTest, parse_empty_line)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n"
    "\n"
    "0\t0\tEXIT\t1\t0\t0\t{}\n");

  schedule = SchedulePtr(new Schedule(inbuf, dummy_path));

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
    "0\t0\tSTORE\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\t0\t0\t0\t{}\n"
    "1\t0\tSTORE\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "1\t0\tSTORE\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "wrong\t0\tSTORE\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t1000\tSTORE\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\tUNKNOWN\tSTORE\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tUNKNOWN\t0\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\tILLEGAL\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: STORE does not support labels", e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_argument_unknown_label)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t5\tJMP\tILLEGAL\t0\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\t0\tILLEGAL\t0\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\t0\t0\tILLEGAL\t{}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        dummy_path + ":3: illegal CAS memory register value [ILLEGAL]",
        e.what());
    }
}

TEST_F(ScheduleTest, parse_illegal_heap)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\tILLEGAL\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\t0\t0\t0\t{ILLEGAL}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\t0\t0\t0\t{(ILLEGAL,0)}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
    "0\t0\tSTORE\t0\t0\t0\t{(0,ILLEGAL)}\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
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
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing CAS memory register value", e.what());
    }
}

TEST_F(ScheduleTest, parse_missing_heap)
{
  istringstream inbuf(
    program_path + "\n"
    ".\n" +
    "0\t0\tSTORE\t0\t0\t0\n");

  try
    {
      schedule = SchedulePtr(new Schedule(inbuf, dummy_path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(dummy_path + ":3: missing heap update", e.what());
    }
}

// void Schedule::push_back_*
using Insert_Data = tuple<unsigned long, word, word, word>;

const vector<Insert_Data> push_back_data {
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

// void Schedule::push_back_thread (const unsigned long step, const word thread)
TEST_F(ScheduleTest, push_back_thread)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, _, __] : push_back_data)
    schedule->push_back_thread(step, thread);

  ASSERT_EQ(push_back_data.size(), schedule->bound);
  ASSERT_EQ(
    Schedule::Update_Map ({
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

// void Schedule::push_back_pc (
//                              const unsigned long step,
//                              const word thread,
//                              const word pc
//                             )
const vector<Schedule::Update_Map> push_back_expected {
  {{1, 0}, {5, 1}, {9, 0}, {13, 1}},
  {{2, 0}, {6, 1}, {10, 0}, {14, 1}}
};

TEST_F(ScheduleTest, push_back_pc)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, pc, _] : push_back_data)
    schedule->push_back_pc(step, thread, pc);

  ASSERT_EQ(push_back_data.size(), schedule->bound);
  ASSERT_EQ(push_back_expected, schedule->pc_updates);
}

// void Schedule::push_back_accu (
//                                const unsigned long step,
//                                const word thread,
//                                const word accu
//                               )
TEST_F(ScheduleTest, push_back_accu)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, accu, _] : push_back_data)
    schedule->push_back_accu(step, thread, accu);

  ASSERT_EQ(push_back_data.size(), schedule->bound);
  ASSERT_EQ(push_back_expected, schedule->accu_updates);
}

// void Schedule::push_back_mem (
//                               const unsigned long step,
//                               const word thread,
//                               const word mem
//                              )
TEST_F(ScheduleTest, push_back_mem)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, mem, _] : push_back_data)
    schedule->push_back_mem(step, thread, mem);

  ASSERT_EQ(push_back_data.size(), schedule->bound);
  ASSERT_EQ(push_back_expected, schedule->mem_updates);
}

// void Schedule::push_back_heap (
//                                const unsigned long step,
//                                const Heap_Cell cell
//                               )
TEST_F(ScheduleTest, push_back_heap)
{
  create_dummy_schedule(2);

  for (const auto & [step, thread, idx, val] : push_back_data)
    schedule->push_back_heap(step, {idx, val});

  ASSERT_EQ(push_back_data.size(), schedule->bound);
  ASSERT_EQ(
    Schedule::Heap_Updates ({
      {0, {{1, 0}, {9, 1}}},
      {1, {{5, 0}, {13, 1}}}
    }),
    schedule->heap_updates);
}

// std::string Schedule::print ()
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

// Schedule::iterator
TEST_F(ScheduleTest, iterator)
{
  schedule = create_from_file<Schedule>(schedule_path);

  word tid[]  = {0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1};
  word pc[]   = {0, 0, 1, 1, 2, 3, 2, 4, 5, 3, 4, 2, 3, 4, 5, 5};
  word accu[] = {0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 2, 1, 1, 0};
  word mem[]  = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0};

  Schedule::iterator it = schedule->begin(), end = schedule->end();

  for (unsigned long i = 0; it != end; i++, ++it)
    {
      ASSERT_EQ(tid[i], it->thread);
      ASSERT_EQ(pc[i], it->pc);
      ASSERT_EQ(accu[i], it->accu);
      ASSERT_EQ(mem[i], it->mem);

      if (i == 0)
        {
          ASSERT_EQ(0, it->heap->idx);
          ASSERT_EQ(0, it->heap->val);
        }
      else if (i == 7)
        {
          ASSERT_EQ(0, it->heap->idx);
          ASSERT_EQ(1, it->heap->val);
        }
      else if (i == 13)
        {
          ASSERT_EQ(0, it->heap->idx);
          ASSERT_EQ(2, it->heap->val);
        }
      else
        ASSERT_FALSE(it->heap);
    }

  /* end() remains end() */
  ASSERT_EQ(it++, end);
  ASSERT_EQ(++it, end);
}

// bool operator == (const Schedule &, const Schedule &)
// bool operator != (const Schedule &, const Schedule &)
TEST_F(ScheduleTest, operator_equals)
{
  ProgramListPtr p1(new ProgramList());
  ProgramListPtr p2(new ProgramList());

  p1->push_back(ProgramPtr(new Program()));
  p1->push_back(ProgramPtr(new Program()));

  p2->push_back(ProgramPtr(new Program()));
  p2->push_back(ProgramPtr(new Program()));

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
  s1.push_back(0, 0, 0, 0, {{1, 0}});
  s1.push_back(1, 0, 0, 0, {});
  s1.push_back(0, 1, 1, 0, {});
  s1.push_back(1, 1, 1, 0, {});

  s2.push_back(0, 0, 0, 0, {{1, 0}});
  s2.push_back(1, 0, 0, 0, {});
  s2.push_back(0, 1, 1, 0, {});
  s2.push_back(1, 1, 1, 0, {});

  ASSERT_TRUE(s1 == s2);

  /* exit codes differ */
  s2.exit = 1;

  ASSERT_TRUE(s1 != s2);

  s2.exit = 0;

  ASSERT_TRUE(s1 == s2);

  /* traces differ */
  Schedule s3 = s2;

  s3.push_back(0, 2, 1, 0, {{1, 1}});

  ASSERT_TRUE(s1 != s3);

  /* programs differ */
  p2->at(1)->push_back(Instruction::Set::create("STORE", 1));

  ASSERT_TRUE(s1 != s2);

  p1->at(1)->push_back(Instruction::Set::create("STORE", 1));

  ASSERT_TRUE(s1 == s2);

  /* list of programs differ */
  p2->push_back(ProgramPtr(new Program()));

  ASSERT_TRUE(s1 != s2);

  p1->push_back(ProgramPtr(new Program()));

  ASSERT_TRUE(s1 == s2);

  /* compare files */
  SchedulePtr sp1 = create_from_file<Schedule>(schedule_path);
  SchedulePtr sp2 = create_from_file<Schedule>(schedule_path);

  ASSERT_TRUE(*sp1 == *sp2);
}
