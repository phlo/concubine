#include <gtest/gtest.h>

#include "parser.hh"
#include "program.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ProgramTest : public ::testing::Test
{
  string path = "dummy.asm";

  ProgramPtr program = ProgramPtr(new Program());
};

/* add ************************************************************************/
TEST_F(ProgramTest, add)
{
  program->push_back(Instruction::Set::create("ADD", 1));
  ASSERT_EQ(1, program->size());
  ASSERT_EQ(0, program->sync_ids.size());

  program->push_back(Instruction::Set::create("SYNC", 1));
  ASSERT_EQ(2, program->size());
  ASSERT_EQ(1, program->sync_ids.size());
  ASSERT_TRUE(program->sync_ids.find(1) != program->sync_ids.end());
}

/* parse **********************************************************************/
TEST_F(ProgramTest, parse)
{
  program = create_from_file<Program>("data/increment.cas.asm");

  ASSERT_EQ(6, program->size());
  ASSERT_EQ(1, program->sync_ids.size());
  ASSERT_EQ(1, program->labels.size());
  ASSERT_EQ(1, program->pc_to_label.size());
  ASSERT_EQ("LOOP", *program->pc_to_label[2]);
  ASSERT_EQ(1, program->label_to_pc.size());
  ASSERT_EQ(2, program->label_to_pc[program->pc_to_label[2]]);

  ASSERT_EQ("0\tSTORE\t0",  program->print(true, 0));
  ASSERT_EQ("1\tSYNC\t0",   program->print(true, 1));
  ASSERT_EQ("LOOP\tMEM\t0", program->print(true, 2));
  ASSERT_EQ("3\tADDI\t1",   program->print(true, 3));
  ASSERT_EQ("4\tCAS\t0",    program->print(true, 4));
  ASSERT_EQ("5\tJMP\tLOOP", program->print(true, 5));

  /* indirect addressing */
  program = create_from_file<Program>("data/indirect.addressing.asm");

  ASSERT_EQ(5, program->size());
  ASSERT_EQ(0, program->sync_ids.size());
  ASSERT_EQ(0, program->labels.size());

  ASSERT_EQ("0\tADDI\t1",     program->print(true, 0));
  ASSERT_EQ("1\tSTORE\t[1]",  program->print(true, 1));
  ASSERT_EQ("2\tLOAD\t1",     program->print(true, 2));
  ASSERT_EQ("3\tADD\t[1]",    program->print(true, 3));
  ASSERT_EQ("4\tCMP\t[1]",    program->print(true, 4));
}

/* parse_empty_line ***********************************************************/
TEST_F(ProgramTest, parse_empty_line)
{
  istringstream inbuf(
    "ADDI 1\n"
    "\n"
    "EXIT 1\n");

  program = ProgramPtr(new Program(inbuf, path));

  ASSERT_EQ(2, program->size());

  ASSERT_EQ("0\tADDI\t1",  program->print(true, 0));
  ASSERT_EQ("1\tEXIT\t1",   program->print(true, 1));
}

/* parse_file_not_found *******************************************************/
TEST_F(ProgramTest, parse_file_not_found)
{
  string file = "file_not_found";

  try
    {
      program = create_from_file<Program>(file);
      ASSERT_TRUE(false);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("file_not_found not found", e.what());
    }
}

/* parse_illegal_instruction **************************************************/
TEST_F(ProgramTest, parse_illegal_instruction)
{
  istringstream inbuf;

  /* illegal instruction */
  inbuf.str("NOP\n");

  try
    {
      program = ProgramPtr(new Program(inbuf, path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: 'NOP' unknown instruction", e.what());
    }

  /* illegal instruction argument (label) */
  inbuf.str("ADD nothing\n");

  try
    {
      program = ProgramPtr(new Program(inbuf, path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: ADD does not support labels", e.what());
    }

  /* illegal instruction argument (indirect addressing) */
  inbuf.str("SYNC [0]\n");

  try
    {
      program = ProgramPtr(new Program(inbuf, path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        path + ":1: SYNC does not support indirect addressing",
        e.what());
    }

  /* illegal instruction argument (label in indirect address) */
  inbuf.str("STORE [me]\n");

  try
    {
      program = ProgramPtr(new Program(inbuf, path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        path + ":1: indirect addressing does not support labels",
        e.what());
    }
}

/* parse_missing_label ********************************************************/
TEST_F(ProgramTest, parse_missing_label)
{
  istringstream inbuf;

  /* missing label */
  inbuf.str(
    "ADDI 1\n"
    "JMP LABEL\n");

  try
    {
      program = ProgramPtr(new Program(inbuf, path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: unknown label [LABEL]", e.what());
      inbuf.clear(); // eof - program fully parsed!
    }

  /* misspelled label */
  inbuf.str(
    "LABEL: ADDI 1\n"
    "JMP LABERL\n");

  try
    {
      program = ProgramPtr(new Program(inbuf, path));
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: unknown label [LABERL]", e.what());
    }
}

/* get_pc *********************************************************************/
TEST_F(ProgramTest, get_pc)
{
  istringstream inbuf(
    "LABEL: ADDI 1\n"
    "JMP LABEL\n");

  program = ProgramPtr(new Program(inbuf, path));

  ASSERT_EQ(0, program->get_pc("LABEL"));

  /* unknown label */
  try
    {
      program->get_pc("UNKNOWN");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("unknown label [UNKNOWN]", e.what());
    }
}

/* get_label ******************************************************************/
TEST_F(ProgramTest, get_label)
{
  istringstream inbuf(
    "LABEL: ADDI 1\n"
    "JMP LABEL\n");

  program = ProgramPtr(new Program(inbuf, path));

  ASSERT_EQ("LABEL", program->get_label(0));

  /* illegal pc */
  try
    {
      program->get_label(word_max);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        "illegal program counter [" + to_string(word_max) + "]",
        e.what());
    }
}

/* operator_equals ************************************************************/
TEST_F(ProgramTest, operator_equals)
{
  Program p1, p2;

  p1.path = "program_1.asm";
  p1.push_back(Instruction::Set::create("LOAD", 1));
  p1.push_back(Instruction::Set::create("ADDI", 1));

  p2.path = "program_1.asm";
  p2.push_back(Instruction::Set::create("LOAD", 1));
  p2.push_back(Instruction::Set::create("ADDI", 1));

  ASSERT_TRUE(p1 == p2);

  /* same programs, different paths */
  p2.path = "program_2.asm";

  ASSERT_TRUE(p1 == p2);

  /* different size */
  p1.push_back(Instruction::Set::create("STORE", 1));

  ASSERT_TRUE(p1 != p2);

  /* different instructions */
  p2.push_back(Instruction::Set::create("JNZ", 0));

  ASSERT_TRUE(p1 != p2);
}
