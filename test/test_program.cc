#include <gtest/gtest.h>

#include "program.hh"

#include "instruction.hh"
#include "parser.hh"

namespace ConcuBinE::test {

//==============================================================================
// Program tests
//==============================================================================

const std::string dummy_path = "dummy.asm";

Program create_program (const std::string & code,
                        const std::string & path = dummy_path)
{
  std::istringstream inbuf(code);
  return Program(inbuf, path);
}

// construction ================================================================

TEST(Program, construction)
{
  auto p1 =
    create_program(
      "start: LOAD 1\n"
      "CHECK 0\n"
      "JMP start\n");

  ASSERT_FALSE(p1.empty());
  ASSERT_FALSE(p1.predecessors.empty());
  ASSERT_FALSE(p1.checkpoints.empty());
  ASSERT_FALSE(p1.pc_to_label.empty());
  ASSERT_FALSE(p1.label_to_pc.empty());

  // copy construction
  Program p2 (p1);
  ASSERT_EQ(p1.size(), p2.size());
  for (size_t i = 0; i < p1.size(); i++)
    ASSERT_NE(&p1[i], &p2[i]);
  ASSERT_EQ(p1, p2);

  const Instruction * ptr = &p1[0];

  // move construction
  Program p3 (std::move(p1));
  ASSERT_TRUE(p1.empty());
  ASSERT_TRUE(p1.path.empty());
  ASSERT_TRUE(p1.predecessors.empty());
  ASSERT_TRUE(p1.checkpoints.empty());
  ASSERT_TRUE(p1.pc_to_label.empty());
  ASSERT_TRUE(p1.label_to_pc.empty());
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
  ASSERT_EQ(p1, p2);
  ASSERT_EQ(ptr, &p2[0]);

  Program::List p {p1, p2};
  std::unique_ptr<Program::List> p_ptr =
    std::make_unique<Program::List>(std::move(p));
  ASSERT_TRUE(p.empty());
  p = std::move(*p_ptr);
  ASSERT_FALSE(p.empty());
}

// parser ======================================================================

TEST(Program, parse)
{
  auto program = create_from_file<Program>("test/data/increment.cas.asm");

  ASSERT_EQ(7, program.size());
  ASSERT_EQ(1, program.checkpoints.size());
  ASSERT_EQ(2, program.checkpoints[0][0]);
  ASSERT_EQ(1, program.pc_to_label.size());
  ASSERT_EQ("LOOP", program.pc_to_label[3]);
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
  program = create_from_file<Program>("test/data/indirect.asm");

  ASSERT_EQ(7, program.size());
  ASSERT_EQ(0, program.checkpoints.size());

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

TEST(Program, parse_empty_line)
{
  auto program =
    create_program(
      "ADDI 1\n"
      "\n"
      "EXIT 1\n");

  ASSERT_EQ(2, program.size());

  ASSERT_EQ("0 ADDI 1", program.print(true, 0));
  ASSERT_EQ("1 EXIT 1", program.print(true, 1));
}

TEST(Program, parse_file_not_found)
{
  try
    {
      create_from_file<Program>("file");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_STREQ("file not found", e.what());
    }
}

TEST(Program, parse_illegal_instruction)
{
  // illegal instruction
  try
    {
      create_program("NOP\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: 'NOP' unknown instruction", e.what());
    }

  // illegal instruction argument (label)
  try
    {
      create_program("ADD nothing\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: 'ADD' does not support labels", e.what());
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
        dummy_path + ":1: 'CHECK' does not support indirect addressing",
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
        dummy_path + ":1: indirect addressing does not support labels",
        e.what());
    }
}

TEST(Program, parse_missing_label)
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
      ASSERT_EQ(dummy_path + ":1: unknown label [LABEL]", e.what());
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
      ASSERT_EQ(dummy_path + ":1: unknown label [LABERL]", e.what());
    }
}

TEST(Program, parse_illegal_jump)
{
  try
    {
      create_program("JMP 1\n");
      FAIL() << "should throw an std::exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": illegal jump [0]", e.what());
    }
}

TEST(Program, parse_predecessors)
{
  auto program =
    create_program(
      "ADDI 1\n"
      "ADDI 1\n"
      "ADDI 1\n");

  ASSERT_EQ(std::set<word_t>(), program.predecessors.at(0));
  ASSERT_EQ(std::set<word_t>({0}), program.predecessors.at(1));
  ASSERT_EQ(std::set<word_t>({1}), program.predecessors.at(2));
}

TEST(Program, parse_predecessors_jnz)
{
  auto program =
    create_program(
      "ADDI 1\n"
      "ADDI 1\n"
      "JNZ 1\n");

  ASSERT_EQ(std::set<word_t>(), program.predecessors.at(0));
  ASSERT_EQ(std::set<word_t>({0, 2}), program.predecessors.at(1));
  ASSERT_EQ(std::set<word_t>({1}), program.predecessors.at(2));
}

TEST(Program, parse_predecessors_jnz_initial)
{
  auto program =
    create_program(
      "ADDI 1\n"
      "ADDI 1\n"
      "JNZ 0\n");

  ASSERT_EQ(std::set<word_t>({2}), program.predecessors.at(0));
  ASSERT_EQ(std::set<word_t>({0}), program.predecessors.at(1));
  ASSERT_EQ(std::set<word_t>({1}), program.predecessors.at(2));
}

TEST(Program, parse_predecessors_jmp)
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
      ASSERT_EQ(dummy_path + ": unreachable instruction [1]", e.what());
    }
}

TEST(Program, parse_predecessors_exit)
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
      ASSERT_EQ(dummy_path + ": unreachable instruction [2]", e.what());
    }
}

TEST(Program, parse_predecessors_halt)
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
      ASSERT_EQ(dummy_path + ": unreachable instruction [2]", e.what());
    }
}

// Program::push_back ==========================================================

TEST(Program, push_back)
{
  Program program;

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

TEST(Program, get_pc)
{
  auto program =
    create_program(
      "LABEL: ADDI 1\n"
      "JMP LABEL\n");

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

TEST(Program, get_label)
{
  auto program =
    create_program(
      "LABEL: ADDI 1\n"
      "JMP LABEL\n");

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

TEST(Program, print)
{
  auto program = create_from_file<Program>("test/data/increment.cas.asm");

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

TEST(Program, operator_equals)
{
  Program p1, p2;

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

//==============================================================================
// Program::List tests
//==============================================================================

// construction ================================================================

TEST(Program, list)
{
  auto p0 = create_program("EXIT 0", "p0.asm");
  auto p1 = create_program("EXIT 0", "p1.asm");

  auto i0 = &p0[0];
  auto i1 = &p1[0];

  // copy construction
  auto lst = Program::List(p0, p1);

  ASSERT_EQ(p0, lst.at(0));
  ASSERT_EQ(p1, lst.at(1));

  ASSERT_NE(i0, &lst.at(0)[0]);
  ASSERT_NE(i1, &lst.at(1)[0]);

  // move construction
  lst = Program::List(std::move(p0), std::move(p1));

  ASSERT_NE(p0, lst.at(0));
  ASSERT_NE(p1, lst.at(1));

  ASSERT_TRUE(p0.empty());
  ASSERT_TRUE(p1.empty());

  ASSERT_EQ(i0, &lst.at(0)[0]);
  ASSERT_EQ(i1, &lst.at(1)[0]);

  ASSERT_TRUE(Program::List().empty());
}

} // namespace ConcuBinE::test
