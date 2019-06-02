#include <gtest/gtest.h>

#include "program.hh"

#include "instructionset.hh"
#include "parser.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ProgramTest : public ::testing::Test
{
  using Predecessors = set<word_t>;

  string path = "dummy.asm";
  Program_ptr program = make_shared<Program>();

  void create_program (string code)
    {
      istringstream inbuf {code};
      program = make_shared<Program>(inbuf, path);
    }
};

/* constructor ****************************************************************/
TEST_F(ProgramTest, parse)
{
  program = create_from_file<Program>("data/increment.cas.asm");

  ASSERT_EQ(6, program->size());
  ASSERT_EQ(1, program->check_ids.size());
  ASSERT_EQ(1, program->labels.size());
  ASSERT_EQ(1, program->pc_to_label.size());
  ASSERT_EQ("LOOP", *program->pc_to_label[2]);
  ASSERT_EQ(1, program->label_to_pc.size());
  ASSERT_EQ(2, program->label_to_pc[program->pc_to_label[2]]);

  ASSERT_EQ("0\tSTORE\t0",  program->print(true, 0));
  ASSERT_EQ("1\tCHECK\t0",  program->print(true, 1));
  ASSERT_EQ("LOOP\tMEM\t0", program->print(true, 2));
  ASSERT_EQ("3\tADDI\t1",   program->print(true, 3));
  ASSERT_EQ("4\tCAS\t0",    program->print(true, 4));
  ASSERT_EQ("5\tJMP\tLOOP", program->print(true, 5));

  /* indirect addressing */
  program = create_from_file<Program>("data/indirect.addressing.asm");

  ASSERT_EQ(6, program->size());
  ASSERT_EQ(0, program->check_ids.size());
  ASSERT_EQ(0, program->labels.size());

  ASSERT_EQ("0\tSTORE\t1",    program->print(true, 0));
  ASSERT_EQ("1\tADDI\t1",     program->print(true, 1));
  ASSERT_EQ("2\tSTORE\t[1]",  program->print(true, 2));
  ASSERT_EQ("3\tLOAD\t[0]",   program->print(true, 3));
  ASSERT_EQ("4\tADD\t[1]",    program->print(true, 4));
  ASSERT_EQ("5\tCMP\t[1]",    program->print(true, 5));
}

TEST_F(ProgramTest, parse_empty_line)
{
  create_program(
    "ADDI 1\n"
    "\n"
    "EXIT 1\n");

  ASSERT_EQ(2, program->size());

  ASSERT_EQ("0\tADDI\t1",  program->print(true, 0));
  ASSERT_EQ("1\tEXIT\t1",   program->print(true, 1));
}

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

TEST_F(ProgramTest, parse_illegal_instruction)
{
  /* illegal instruction */
  try
    {
      create_program("NOP\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: 'NOP' unknown instruction", e.what());
    }

  /* illegal instruction argument (label) */
  try
    {
      create_program("ADD nothing\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: 'ADD' does not support labels", e.what());
    }

  /* illegal instruction argument (indirect addressing) */
  try
    {
      create_program("CHECK [0]\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        path + ":1: 'CHECK' does not support indirect addressing",
        e.what());
    }

  /* illegal instruction argument (label in indirect address) */
  try
    {
      create_program("STORE [me]\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        path + ":1: indirect addressing does not support labels",
        e.what());
    }
}

TEST_F(ProgramTest, parse_missing_label)
{
  /* missing label */
  try
    {
      create_program(
        "ADDI 1\n"
        "JMP LABEL\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: unknown label [LABEL]", e.what());
    }

  /* misspelled label */
  try
    {
      create_program(
        "LABEL: ADDI 1\n"
        "JMP LABERL\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: unknown label [LABERL]", e.what());
    }
}

TEST_F(ProgramTest, parse_illegal_jump)
{
  try
    {
      create_program("JMP 1\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ": illegal jump [0]", e.what());
    }
}

TEST_F(ProgramTest, parse_predecessors)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "ADDI 1\n");

  ASSERT_EQ(Predecessors(), program->predecessors.at(0));
  ASSERT_EQ(Predecessors({0}), program->predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program->predecessors.at(2));
}

TEST_F(ProgramTest, parse_predecessors_jnz)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "JNZ 1\n");

  ASSERT_EQ(Predecessors(), program->predecessors.at(0));
  ASSERT_EQ(Predecessors({0, 2}), program->predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program->predecessors.at(2));
}

TEST_F(ProgramTest, parse_predecessors_jnz_initial)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "JNZ 0\n");

  ASSERT_EQ(Predecessors({2}), program->predecessors.at(0));
  ASSERT_EQ(Predecessors({0}), program->predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program->predecessors.at(2));
}

TEST_F(ProgramTest, parse_predecessors_jmp)
{
  try
    {
      create_program(
        "JMP 2\n"
        "ADDI 1\n"
        "ADDI 1\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ": unreachable instruction [1]", e.what());
    }
}

TEST_F(ProgramTest, parse_predecessors_exit)
{
  try
    {
      create_program(
        "ADDI 1\n"
        "EXIT 1\n"
        "ADDI 1\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ": unreachable instruction [2]", e.what());
    }
}

TEST_F(ProgramTest, parse_predecessors_halt)
{
  try
    {
      create_program(
        "ADDI 1\n"
        "HALT\n"
        "ADDI 1\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ": unreachable instruction [2]", e.what());
    }
}

/* Program::push_back *********************************************************/
TEST_F(ProgramTest, push_back)
{
  program->push_back(Instruction::Set::create("ADD", 1));
  ASSERT_EQ(1, program->size());
  ASSERT_EQ(0, program->check_ids.size());

  program->push_back(Instruction::Set::create("CHECK", 1));
  ASSERT_EQ(2, program->size());
  ASSERT_EQ(1, program->check_ids.size());
  ASSERT_TRUE(program->check_ids.find(1) != program->check_ids.end());
}

/* Program::get_pc ************************************************************/
TEST_F(ProgramTest, get_pc)
{
  istringstream inbuf(
    "LABEL: ADDI 1\n"
    "JMP LABEL\n");

  program = make_shared<Program>(inbuf, path);

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

/* Program::get_label *********************************************************/
TEST_F(ProgramTest, get_label)
{
  istringstream inbuf(
    "LABEL: ADDI 1\n"
    "JMP LABEL\n");

  program = make_shared<Program>(inbuf, path);

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
        "no label for program counter [" + to_string(word_max) + "]",
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
