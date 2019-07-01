#include <gtest/gtest.h>

#include "program.hh"

#include "instruction.hh"
#include "parser.hh"

using namespace std;

//==============================================================================
// Program tests
//==============================================================================

struct Program_Test : public ::testing::Test
{
  using Predecessors = set<word_t>;

  string path = "dummy.asm";
  Program program;

  void create_program (string code)
    {
      istringstream inbuf {code};
      program = Program(inbuf, path);
    }
};

// construction ================================================================

TEST_F(Program_Test, construction)
{
  create_program(
    "start: LOAD 1\n"
    "JMP start\n"
  );

  Program & p1 = program;
  ASSERT_FALSE(p1.empty());
  ASSERT_FALSE(p1.labels.empty());

  // copy construction
  Program p2 (p1);
  ASSERT_NE(&p1[0], &p2[0]);
  ASSERT_EQ(p1, p2);

  const Instruction * ptr = &p1[0];

  // move construction
  Program p3 (move(p1));
  ASSERT_TRUE(p1.empty());
  ASSERT_TRUE(p1.path.empty());
  ASSERT_TRUE(p1.predecessors.empty());
  ASSERT_TRUE(p1.checkpoints.empty());
  ASSERT_TRUE(p1.pc_to_label.empty());
  ASSERT_TRUE(p1.label_to_pc.empty());
  ASSERT_TRUE(p1.labels.empty());
  ASSERT_EQ(p2, p3);
  ASSERT_EQ(ptr, &p3[0]);

  // copy assignment
  p1 = p2;
  ASSERT_EQ(p1, p3);
  ASSERT_NE(&p1[0], &p2[0]);
  ASSERT_NE(&p1[0], &p3[0]);

  // move assignment
  p2 = move(p3);
  ASSERT_TRUE(p3.empty());
  ASSERT_TRUE(p3.path.empty());
  ASSERT_TRUE(p3.predecessors.empty());
  ASSERT_TRUE(p3.checkpoints.empty());
  ASSERT_TRUE(p3.pc_to_label.empty());
  ASSERT_TRUE(p3.label_to_pc.empty());
  ASSERT_TRUE(p3.labels.empty());
  ASSERT_EQ(p1, p2);
  ASSERT_EQ(ptr, &p2[0]);

  Program::List p {p1, p2};
  unique_ptr<Program::List> p_ptr = make_unique<Program::List>(move(p));
  ASSERT_TRUE(p.empty());
  p = move(*p_ptr);
  ASSERT_FALSE(p.empty());
}

// parser ======================================================================

TEST_F(Program_Test, parse)
{
  program = create_from_file<Program>("data/increment.cas.asm");

  ASSERT_EQ(7, program.size());
  ASSERT_EQ(1, program.checkpoints.size());
  ASSERT_EQ(1, program.labels.size());
  ASSERT_EQ(1, program.pc_to_label.size());
  ASSERT_EQ("LOOP", *program.pc_to_label[3]);
  ASSERT_EQ(1, program.label_to_pc.size());
  ASSERT_EQ(3, program.label_to_pc[program.pc_to_label[3]]);

  ASSERT_EQ("0\tSTORE\t0",  program.print(true, 0));
  ASSERT_EQ("1\tFENCE\t",   program.print(true, 1));
  ASSERT_EQ("2\tCHECK\t0",  program.print(true, 2));
  ASSERT_EQ("LOOP\tMEM\t0", program.print(true, 3));
  ASSERT_EQ("4\tADDI\t1",   program.print(true, 4));
  ASSERT_EQ("5\tCAS\t0",    program.print(true, 5));
  ASSERT_EQ("6\tJMP\tLOOP", program.print(true, 6));

  // indirect addressing
  program = create_from_file<Program>("data/indirect.addressing.asm");

  ASSERT_EQ(6, program.size());
  ASSERT_EQ(0, program.checkpoints.size());
  ASSERT_EQ(0, program.labels.size());

  ASSERT_EQ("0\tSTORE\t1",    program.print(true, 0));
  ASSERT_EQ("1\tADDI\t1",     program.print(true, 1));
  ASSERT_EQ("2\tSTORE\t[1]",  program.print(true, 2));
  ASSERT_EQ("3\tLOAD\t[0]",   program.print(true, 3));
  ASSERT_EQ("4\tADD\t[1]",    program.print(true, 4));
  ASSERT_EQ("5\tCMP\t[1]",    program.print(true, 5));
}

TEST_F(Program_Test, parse_empty_line)
{
  create_program(
    "ADDI 1\n"
    "\n"
    "EXIT 1\n");

  ASSERT_EQ(2, program.size());

  ASSERT_EQ("0\tADDI\t1",  program.print(true, 0));
  ASSERT_EQ("1\tEXIT\t1",   program.print(true, 1));
}

TEST_F(Program_Test, parse_file_not_found)
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

TEST_F(Program_Test, parse_illegal_instruction)
{
  // illegal instruction
  try
    {
      create_program("NOP\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: 'NOP' unknown instruction", e.what());
    }

  // illegal instruction argument (label)
  try
    {
      create_program("ADD nothing\n");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(path + ":1: 'ADD' does not support labels", e.what());
    }

  // illegal instruction argument (indirect addressing)
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

  // illegal instruction argument (label in indirect address)
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

TEST_F(Program_Test, parse_missing_label)
{
  // missing label
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

  // misspelled label
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

TEST_F(Program_Test, parse_illegal_jump)
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

TEST_F(Program_Test, parse_predecessors)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "ADDI 1\n");

  ASSERT_EQ(Predecessors(), program.predecessors.at(0));
  ASSERT_EQ(Predecessors({0}), program.predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program.predecessors.at(2));
}

TEST_F(Program_Test, parse_predecessors_jnz)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "JNZ 1\n");

  ASSERT_EQ(Predecessors(), program.predecessors.at(0));
  ASSERT_EQ(Predecessors({0, 2}), program.predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program.predecessors.at(2));
}

TEST_F(Program_Test, parse_predecessors_jnz_initial)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "JNZ 0\n");

  ASSERT_EQ(Predecessors({2}), program.predecessors.at(0));
  ASSERT_EQ(Predecessors({0}), program.predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program.predecessors.at(2));
}

TEST_F(Program_Test, parse_predecessors_jmp)
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

TEST_F(Program_Test, parse_predecessors_exit)
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

TEST_F(Program_Test, parse_predecessors_halt)
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

// Program::push_back ==========================================================

TEST_F(Program_Test, push_back)
{
  program.push_back(Instruction::Set::create("ADD", 1));
  ASSERT_EQ(1, program.size());
  ASSERT_EQ(0, program.checkpoints.size());

  program.push_back(Instruction::Set::create("CHECK", 1));
  ASSERT_EQ(2, program.size());
  ASSERT_EQ(1, program.checkpoints.size());
  ASSERT_TRUE(program.checkpoints.find(1) != program.checkpoints.end());
  ASSERT_EQ(vector<word_t>({1}), program.checkpoints[1]);
}

// Program::get_pc =============================================================

TEST_F(Program_Test, get_pc)
{
  create_program(
    "LABEL: ADDI 1\n"
    "JMP LABEL\n"
  );

  ASSERT_EQ(0, program.get_pc("LABEL"));

  // unknown label
  try
    {
      program.get_pc("UNKNOWN");
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("unknown label [UNKNOWN]", e.what());
    }
}

// Program::get_label ==========================================================

TEST_F(Program_Test, get_label)
{
  create_program(
    "LABEL: ADDI 1\n"
    "JMP LABEL\n"
  );

  ASSERT_EQ("LABEL", program.get_label(0));

  // illegal pc
  try
    {
      program.get_label(word_max);
      FAIL() << "should throw an exception";
    }
  catch (const exception & e)
    {
      ASSERT_EQ(
        "no label for program counter [" + to_string(word_max) + "]",
        e.what());
    }
}

// operator equals =============================================================

TEST_F(Program_Test, operator_equals)
{
  Program p1, p2;

  p1.path = "program_1.asm";
  p1.push_back(Instruction::Set::create("LOAD", 1));
  p1.push_back(Instruction::Set::create("ADDI", 1));

  p2.path = "program_1.asm";
  p2.push_back(Instruction::Set::create("LOAD", 1));
  p2.push_back(Instruction::Set::create("ADDI", 1));

  ASSERT_TRUE(p1 == p2);

  // same programs, different paths
  p2.path = "program_2.asm";

  ASSERT_TRUE(p1 == p2);

  // different size
  p1.push_back(Instruction::Set::create("STORE", 1));

  ASSERT_TRUE(p1 != p2);

  // different instructions
  p2.push_back(Instruction::Set::create("JNZ", 0));

  ASSERT_TRUE(p1 != p2);
}
