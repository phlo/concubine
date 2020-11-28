/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include <gtest/gtest.h>

#include "publicate.hh"

#include "program.hh"

#include "instruction.hh"
#include "parser.hh"

namespace ConcuBinE::test {

//==============================================================================
// Program tests
//==============================================================================

const std::string dummy_path = "dummy.asm";

inline Program prog (const std::string & code,
                     const std::string & path = dummy_path)
{
  std::istringstream inbuf(code);
  return Program(inbuf, path);
}

// construction ================================================================

TEST(Program, construction)
{
  auto p1 =
    prog(
      "start: LOAD 1\n"
      "CHECK 0\n"
      "JMP start\n");

  ASSERT_FALSE(p1.empty());
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
  ASSERT_EQ(1, program.pc_to_label.size());
  ASSERT_EQ("LOOP", program.pc_to_label[3]);
  ASSERT_EQ(1, program.label_to_pc.size());
  ASSERT_EQ(3, program.label_to_pc[program.pc_to_label[3]]);
  ASSERT_EQ(
    "STORE 0\n"
    "FENCE\n"
    "CHECK 0\n"
    "LOOP: MEM 0\n"
    "ADDI 1\n"
    "CAS 0\n"
    "JMP LOOP\n",
    program.print());
}

TEST(Program, parse_indirect)
{
  auto program = create_from_file<Program>("test/data/indirect.asm");

  ASSERT_EQ(7, program.size());
  ASSERT_EQ(
    "STORE 1\n"
    "ADDI 1\n"
    "STORE [1]\n"
    "LOAD [0]\n"
    "ADD [1]\n"
    "CMP [1]\n"
    "HALT\n",
    program.print());
}

TEST(Program, parse_empty_line)
{
  auto program =
    prog(
      "ADDI 1\n"
      "\n"
      "EXIT 1\n");

  ASSERT_EQ(2, program.size());
  ASSERT_EQ("ADDI 1", program.print(0));
  ASSERT_EQ("EXIT 1", program.print(1));
}

TEST(Program, parse_file_not_found)
{
  try
    {
      create_from_file<Program>("file");
      FAIL() << "should throw an exception";
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
      prog("NOP\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: 'NOP' unknown instruction", e.what());
    }

  // illegal instruction argument (label)
  try
    {
      prog("ADD nothing\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ":1: 'ADD' does not support labels", e.what());
    }

  // illegal instruction argument (indirect addressing)
  try
    {
      prog("CHECK [0]\n");
      FAIL() << "should throw an exception";
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
      prog("STORE [me]\n");
      FAIL() << "should throw an exception";
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
      prog(
        "ADDI 1\n"
        "JMP LABEL\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": unknown label [LABEL]", e.what());
    }

  // misspelled label
  try
    {
      prog(
        "LABEL: ADDI 1\n"
        "JMP LABERL\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": unknown label [LABERL]", e.what());
    }
}

TEST(Program, parse_illegal_jump)
{
  try
    {
      prog("JMP 1\n");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": illegal jump [0]", e.what());
    }
}

// Program::predecessors =======================================================

TEST(Program, predecessors)
{
  auto predecessors =
    prog(
      "ADDI 1\n"
      "ADDI 1\n"
      "ADDI 1\n")
      .predecessors();

  ASSERT_EQ(std::set<word_t>({0}), predecessors.at(1));
  ASSERT_EQ(std::set<word_t>({1}), predecessors.at(2));
}

TEST(Program, predecessors_jnz)
{
  auto predecessors =
    prog(
      "ADDI 1\n"
      "ADDI 1\n"
      "JNZ 1\n")
      .predecessors();

  ASSERT_EQ(std::set<word_t>({0, 2}), predecessors.at(1));
  ASSERT_EQ(std::set<word_t>({1}), predecessors.at(2));
}

TEST(Program, predecessors_jnz_initial)
{
  auto predecessors =
    prog(
      "ADDI 1\n"
      "ADDI 1\n"
      "JNZ 0\n")
      .predecessors();

  ASSERT_EQ(std::set<word_t>({2}), predecessors.at(0));
  ASSERT_EQ(std::set<word_t>({0}), predecessors.at(1));
  ASSERT_EQ(std::set<word_t>({1}), predecessors.at(2));
}

TEST(Program, predecessors_unreachable_jmp)
{
  try
    {
      prog(
        "JMP 2\n"
        "ADDI 1\n"
        "ADDI 1\n")
        .predecessors();
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": unreachable instruction [1]", e.what());
    }
}

TEST(Program, predecessors_unreachable_halt)
{
  try
    {
      prog(
        "ADDI 1\n"
        "HALT\n"
        "ADDI 1\n")
        .predecessors();
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": unreachable instruction [2]", e.what());
    }
}

TEST(Program, predecessors_unreachable_exit)
{
  try
    {
      prog(
        "ADDI 1\n"
        "EXIT 1\n"
        "ADDI 1\n")
        .predecessors();
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": unreachable instruction [2]", e.what());
    }
}

// Program::pc =================================================================

TEST(Program, pc)
{
  auto program =
    prog(
      "LABEL: ADDI 1\n"
      "JMP LABEL\n");

  ASSERT_EQ(0, program.pc("LABEL"));

  // unknown label
  try
    {
      program.pc("UNKNOWN");
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(dummy_path + ": unknown label [UNKNOWN]", e.what());
    }
}

// Program::label ==============================================================

TEST(Program, label)
{
  auto program =
    prog(
      "LABEL: ADDI 1\n"
      "JMP LABEL\n");

  ASSERT_EQ("LABEL", program.label(0));

  // illegal pc
  try
    {
      program.label(word_max);
      FAIL() << "should throw an exception";
    }
  catch (const std::exception & e)
    {
      ASSERT_EQ(
        dummy_path + ": no label for [" + std::to_string(word_max) + "]",
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
}

// operator equals =============================================================

TEST(Program, operator_equals)
{
  const std::string code = "LOAD 1\nADDI 1";
  const std::string path = "p.asm";

  auto p0 = prog(code, path);
  auto p1 = prog(code, path);

  ASSERT_TRUE(p0 == p1);

  // same programs, different paths
  p1.path = "p1.asm";

  ASSERT_TRUE(p0 == p1);

  // different size
  p0.push_back(Instruction::create("STORE", 1));

  ASSERT_TRUE(p0 != p1);

  p1.push_back(Instruction::create("STORE", 1));

  ASSERT_TRUE(p0 == p1);

  // different instructions
  p0.push_back(Instruction::create("JNZ", 0));
  p1.push_back(Instruction::create("JNZ", 1));

  ASSERT_TRUE(p0 != p1);
}

//==============================================================================
// Program::List tests
//==============================================================================

// construction ================================================================

TEST(Program, list)
{
  auto p0 = prog("EXIT 0", "p0.asm");
  auto p1 = prog("EXIT 0", "p1.asm");

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
