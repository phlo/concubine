#include <gtest/gtest.h>

#include "program.hh"

#include "instruction.hh"
#include "parser.hh"

namespace ConcuBinE::test {

//==============================================================================
// Program tests
//==============================================================================

struct Program : public ::testing::Test
{
  using Predecessors = std::set<word_t>;

  std::string path = "dummy.asm";

  ConcuBinE::Program program;

  void create_program (std::string code)
    {
      std::istringstream inbuf {code};
      program = ConcuBinE::Program(inbuf, path);
    }
};

// construction ================================================================

TEST_F(Program, construction)
{
  create_program(
    "start: LOAD 1\n"
    "JMP start\n"
  );

  ConcuBinE::Program & p1 = program;
  ASSERT_FALSE(p1.empty());
  ASSERT_FALSE(p1.labels.empty());

  // copy construction
  ConcuBinE::Program p2 (p1);
  ASSERT_NE(&p1[0], &p2[0]);
  ASSERT_EQ(p1, p2);

  const Instruction * ptr = &p1[0];

  // std::move construction
  ConcuBinE::Program p3 (std::move(p1));
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

  // std::move assignment
  p2 = std::move(p3);
  ASSERT_TRUE(p3.empty());
  ASSERT_TRUE(p3.path.empty());
  ASSERT_TRUE(p3.predecessors.empty());
  ASSERT_TRUE(p3.checkpoints.empty());
  ASSERT_TRUE(p3.pc_to_label.empty());
  ASSERT_TRUE(p3.label_to_pc.empty());
  ASSERT_TRUE(p3.labels.empty());
  ASSERT_EQ(p1, p2);
  ASSERT_EQ(ptr, &p2[0]);

  ConcuBinE::Program::List p {p1, p2};
  std::unique_ptr<ConcuBinE::Program::List> p_ptr =
    std::make_unique<ConcuBinE::Program::List>(std::move(p));
  ASSERT_TRUE(p.empty());
  p = std::move(*p_ptr);
  ASSERT_FALSE(p.empty());
}

// parser ======================================================================

TEST_F(Program, parse)
{
  program = create_from_file<ConcuBinE::Program>("data/increment.cas.asm");

  ASSERT_EQ(7, program.size());
  ASSERT_EQ(1, program.checkpoints.size());
  ASSERT_EQ(2, program.checkpoints[0][0]);
  ASSERT_EQ(1, program.labels.size());
  ASSERT_EQ(1, program.pc_to_label.size());
  ASSERT_EQ("LOOP", *program.pc_to_label[3]);
  ASSERT_EQ(1, program.label_to_pc.size());
  ASSERT_EQ(3, program.label_to_pc[program.pc_to_label[3]]);

  ASSERT_EQ(
    "0 STORE 0\n"
    "1 FENCE\n"
    "2 CHECK 0\n"
    "3 LOOP: MEM 0\n"
    "4 ADDI 1\n"
    "5 CAS 0\n"
    "6 JMP LOOP\n",
    program.print(true));

  // indirect addressing
  program =
    create_from_file<ConcuBinE::Program>("data/indirect.addressing.asm");

  ASSERT_EQ(7, program.size());
  ASSERT_EQ(0, program.checkpoints.size());
  ASSERT_EQ(0, program.labels.size());

  ASSERT_EQ(
    "0 STORE 1\n"
    "1 ADDI 1\n"
    "2 STORE [1]\n"
    "3 LOAD [0]\n"
    "4 ADD [1]\n"
    "5 CMP [1]\n"
    "6 HALT\n",
    program.print(true));
}

TEST_F(Program, parse_empty_line)
{
  create_program(
    "ADDI 1\n"
    "\n"
    "EXIT 1\n");

  ASSERT_EQ(2, program.size());

  ASSERT_EQ("0 ADDI 1", program.print(true, 0));
  ASSERT_EQ("1 EXIT 1", program.print(true, 1));
}

TEST_F(Program, parse_file_not_found)
{
  try
    {
      program = create_from_file<ConcuBinE::Program>("file");
      ASSERT_TRUE(false);
    }
  catch (const std::exception & e)
    {
      ASSERT_STREQ("file not found", e.what());
    }
}

TEST_F(Program, parse_illegal_instruction)
{
  // illegal instruction
  try
    {
      create_program("NOP\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: 'NOP' unknown instruction", e.what());
    }

  // illegal instruction argument (label)
  try
    {
      create_program("ADD nothing\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: 'ADD' does not support labels", e.what());
    }

  // illegal instruction argument (indirect addressing)
  try
    {
      create_program("CHECK [0]\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        path + ":1: 'CHECK' does not support indirect addressing",
        e.what());
    }

  // illegal instruction argument (label in indirect address)
  try
    {
      create_program("STORE [me]\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        path + ":1: indirect addressing does not support labels",
        e.what());
    }
}

TEST_F(Program, parse_missing_label)
{
  // missing label
  try
    {
      create_program(
        "ADDI 1\n"
        "JMP LABEL\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: unknown label [LABEL]", e.what());
    }

  // misspelled label
  try
    {
      create_program(
        "LABEL: ADDI 1\n"
        "JMP LABERL\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ":1: unknown label [LABERL]", e.what());
    }
}

TEST_F(Program, parse_illegal_jump)
{
  try
    {
      create_program("JMP 1\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ": illegal jump [0]", e.what());
    }
}

TEST_F(Program, parse_predecessors)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "ADDI 1\n");

  ASSERT_EQ(Predecessors(), program.predecessors.at(0));
  ASSERT_EQ(Predecessors({0}), program.predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program.predecessors.at(2));
}

TEST_F(Program, parse_predecessors_jnz)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "JNZ 1\n");

  ASSERT_EQ(Predecessors(), program.predecessors.at(0));
  ASSERT_EQ(Predecessors({0, 2}), program.predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program.predecessors.at(2));
}

TEST_F(Program, parse_predecessors_jnz_initial)
{
  create_program(
    "ADDI 1\n"
    "ADDI 1\n"
    "JNZ 0\n");

  ASSERT_EQ(Predecessors({2}), program.predecessors.at(0));
  ASSERT_EQ(Predecessors({0}), program.predecessors.at(1));
  ASSERT_EQ(Predecessors({1}), program.predecessors.at(2));
}

TEST_F(Program, parse_predecessors_jmp)
{
  try
    {
      create_program(
        "JMP 2\n"
        "ADDI 1\n"
        "ADDI 1\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ": unreachable instruction [1]", e.what());
    }
}

TEST_F(Program, parse_predecessors_exit)
{
  try
    {
      create_program(
        "ADDI 1\n"
        "EXIT 1\n"
        "ADDI 1\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ": unreachable instruction [2]", e.what());
    }
}

TEST_F(Program, parse_predecessors_halt)
{
  try
    {
      create_program(
        "ADDI 1\n"
        "HALT\n"
        "ADDI 1\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(path + ": unreachable instruction [2]", e.what());
    }
}

// Program::push_back ==========================================================

TEST_F(Program, push_back)
{
  program.push_back(Instruction::create("ADD", 1));
  ASSERT_EQ(1, program.size());
  ASSERT_EQ(0, program.checkpoints.size());

  program.push_back(Instruction::create("CHECK", 1));
  ASSERT_EQ(2, program.size());
  ASSERT_EQ(1, program.checkpoints.size());
  ASSERT_TRUE(program.checkpoints.find(1) != program.checkpoints.end());
  ASSERT_EQ(std::vector<word_t>({1}), program.checkpoints[1]);
}

// Program::get_pc =============================================================

TEST_F(Program, get_pc)
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
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_STREQ("unknown label [UNKNOWN]", e.what());
    }
}

// Program::get_label ==========================================================

TEST_F(Program, get_label)
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
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        "no label for program counter [" + std::to_string(word_max) + "]",
        e.what());
    }
}

// Program::print ==============================================================

TEST_F(Program, print)
{
  program = create_from_file<ConcuBinE::Program>("data/increment.cas.asm");

  ASSERT_EQ(
    "STORE 0\n"
    "FENCE\n"
    "CHECK 0\n"
    "LOOP: MEM 0\n"
    "ADDI 1\n"
    "CAS 0\n"
    "JMP LOOP\n",
    program.print());

  // include pc
  ASSERT_EQ(
    "0 STORE 0\n"
    "1 FENCE\n"
    "2 CHECK 0\n"
    "3 LOOP: MEM 0\n"
    "4 ADDI 1\n"
    "5 CAS 0\n"
    "6 JMP LOOP\n",
    program.print(true));
}

// operator equals =============================================================

TEST_F(Program, operator_equals)
{
  ConcuBinE::Program p1, p2;

  p1.path = "program_1.asm";
  p1.push_back(Instruction::create("LOAD", 1));
  p1.push_back(Instruction::create("ADDI", 1));

  p2.path = "program_1.asm";
  p2.push_back(Instruction::create("LOAD", 1));
  p2.push_back(Instruction::create("ADDI", 1));

  ASSERT_TRUE(p1 == p2);

  // same programs, different paths
  p2.path = "program_2.asm";

  ASSERT_TRUE(p1 == p2);

  // different size
  p1.push_back(Instruction::create("STORE", 1));

  ASSERT_TRUE(p1 != p2);

  // different instructions
  p2.push_back(Instruction::create("JNZ", 0));

  ASSERT_TRUE(p1 != p2);
}

} // namespace ConcuBinE::test
