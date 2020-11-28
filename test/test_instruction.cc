/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include <gtest/gtest.h>

#include "publicate.hh"

#include "instruction.hh"

namespace ConcuBinE::test {

//==============================================================================
// Instruction tests
//==============================================================================

using Type = ConcuBinE::Instruction::Type;

// construction ================================================================

TEST(Instruction, construction)
{
  ConcuBinE::Instruction op1(ConcuBinE::Instruction::create("LOAD", 1, true));
  ConcuBinE::Instruction::Concept * base = op1.model.get();

  // copy construction
  ConcuBinE::Instruction op2(op1);
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_NE(op1.model.get(), op2.model.get());

  // move construction
  ConcuBinE::Instruction op3(std::move(op1));
  ASSERT_FALSE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_TRUE(op3.model);
  ASSERT_EQ(base, op3.model.get());
  ASSERT_NE(op2.model.get(), op3.model.get());

  // copy assignment
  op1 = op2;
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_TRUE(op3.model);
  ASSERT_NE(op1.model.get(), op2.model.get());
  ASSERT_NE(op1.model.get(), op3.model.get());

  // move assignment
  op2 = std::move(op3);
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_FALSE(op3.model);
  ASSERT_NE(op1.model.get(), op2.model.get());
  ASSERT_EQ(base, op2.model.get());
}

// Instruction::create =========================================================

TEST(Instruction, create)
{
  // normal
  auto op = ConcuBinE::Instruction::create("EXIT", 0);

  ASSERT_EQ("EXIT", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(0, op.arg());

  // negative arg
  op = ConcuBinE::Instruction::create("LOAD", static_cast<word_t>(-1));

  ASSERT_EQ("LOAD", op.symbol());
  ASSERT_EQ(Type::accu | Type::read, op.type());
  ASSERT_EQ(word_max, op.arg());

  // arg overflow
  op = ConcuBinE::Instruction::create("LOAD", word_t(word_max + 1));

  ASSERT_EQ("LOAD", op.symbol());
  ASSERT_EQ(Type::accu | Type::read, op.type());
  ASSERT_EQ(0, op.arg());

  // unknown op
  try { op = ConcuBinE::Instruction::create("NOP"); } catch (...) {}
  try { op = ConcuBinE::Instruction::create("NOP", 0); } catch (...) {}
}

// Instruction::contains =======================================================

TEST(Instruction, contains)
{
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("LOAD"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("STORE"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("FENCE"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("ADD"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("ADDI"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("SUB"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("SUBI"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("CMP"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("JMP"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("JZ"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("JNZ"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("JS"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("JNS"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("JNZNS"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("MEM"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("CAS"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("CHECK"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("HALT"));
  ASSERT_EQ(true, ConcuBinE::Instruction::contains("EXIT"));

  ASSERT_EQ(false, ConcuBinE::Instruction::contains("NOP"));
}

// Instruction::type ===========================================================

TEST(Instruction, type)
{
  auto op = ConcuBinE::Instruction::create("EXIT", 0);

  ASSERT_EQ(Type::control, op.type());

  op.type(Type::none);
  ASSERT_EQ(Type::none, op.type());
}

// Instruction::arg ============================================================

TEST(Instruction, arg)
{
  auto op = ConcuBinE::Instruction::create("EXIT", 1);

  ASSERT_EQ(1, op.arg());

  op.arg(0);
  ASSERT_EQ(0, op.arg());
}

// Instruction::indirect =======================================================

TEST(Instruction, indirect)
{
  auto op = ConcuBinE::Instruction::create("LOAD", 0);

  ASSERT_FALSE(op.indirect());

  op.indirect(true);
  ASSERT_TRUE(op.indirect());
}

// operators ===================================================================

TEST(Instruction, operator_equals)
{
  // Nullary
  ASSERT_EQ(
    ConcuBinE::Instruction::create("FENCE"),
    ConcuBinE::Instruction::create("FENCE"));

  ASSERT_NE(
    ConcuBinE::Instruction::create("FENCE"),
    ConcuBinE::Instruction::create("HALT"));

  // Unary
  ASSERT_EQ(
    ConcuBinE::Instruction::create("ADDI", 1),
    ConcuBinE::Instruction::create("ADDI", 1));

  ASSERT_NE(
    ConcuBinE::Instruction::create("ADDI", 1),
    ConcuBinE::Instruction::create("ADDI", 2));

  ASSERT_NE(
    ConcuBinE::Instruction::create("ADDI", 1),
    ConcuBinE::Instruction::create("SUBI", 1));

  // Memory
  ASSERT_EQ(
    ConcuBinE::Instruction::create("STORE", 1),
    ConcuBinE::Instruction::create("STORE", 1));

  ASSERT_NE(
    ConcuBinE::Instruction::create("STORE", 1),
    ConcuBinE::Instruction::create("STORE", 2));

  ASSERT_NE(
    ConcuBinE::Instruction::create("STORE", 1, true),
    ConcuBinE::Instruction::create("STORE", 1, false));

  ASSERT_NE(
    ConcuBinE::Instruction::create("STORE", 1),
    ConcuBinE::Instruction::create("LOAD", 1));
}

// LOAD ========================================================================

TEST(Instruction, LOAD)
{
  const auto op = ConcuBinE::Instruction::create("LOAD", 0);

  ASSERT_EQ("LOAD", op.symbol());
  ASSERT_EQ(Type::accu | Type::read, op.type());
  ASSERT_EQ(0, op.arg());
}

// STORE =======================================================================

TEST(Instruction, STORE)
{
  const auto op = ConcuBinE::Instruction::create("STORE", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_TRUE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_TRUE(op.requires_flush());

  ASSERT_EQ("STORE", op.symbol());
  ASSERT_EQ(Type::write, op.type());
  ASSERT_EQ(0, op.arg());
  ASSERT_FALSE(op.indirect());
}

// FENCE =======================================================================

TEST(Instruction, FENCE)
{
  const auto op = ConcuBinE::Instruction::create("FENCE");

  ASSERT_TRUE(op.is_nullary());
  ASSERT_FALSE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_TRUE(op.requires_flush());

  ASSERT_EQ("FENCE", op.symbol());
  ASSERT_EQ(Type::barrier, op.type());
}

// ADD =========================================================================

TEST(Instruction, ADD)
{
  const auto op = ConcuBinE::Instruction::create("ADD", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_TRUE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("ADD", op.symbol());
  ASSERT_EQ(Type::accu | Type::read, op.type());
  ASSERT_EQ(0, op.arg());
  ASSERT_FALSE(op.indirect());
}

// ADDI ========================================================================

TEST(Instruction, ADDI)
{
  const auto op = ConcuBinE::Instruction::create("ADDI", 1);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("ADDI", op.symbol());
  ASSERT_EQ(Type::accu, op.type());
  ASSERT_EQ(1, op.arg());
}

// SUB =========================================================================

TEST(Instruction, SUB)
{
  const auto op = ConcuBinE::Instruction::create("SUB", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_TRUE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("SUB", op.symbol());
  ASSERT_EQ(Type::accu | Type::read, op.type());
  ASSERT_EQ(0, op.arg());
  ASSERT_FALSE(op.indirect());
}

// SUBI ========================================================================

TEST(Instruction, SUBI)
{
  const auto op = ConcuBinE::Instruction::create("SUBI", 1);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("SUBI", op.symbol());
  ASSERT_EQ(Type::accu, op.type());
  ASSERT_EQ(1, op.arg());
}

// MUL =========================================================================

TEST(Instruction, MUL)
{
  const auto op = ConcuBinE::Instruction::create("MUL", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_TRUE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("MUL", op.symbol());
  ASSERT_EQ(Type::accu | Type::read, op.type());
  ASSERT_EQ(0, op.arg());
  ASSERT_FALSE(op.indirect());
}

// MULI ========================================================================

TEST(Instruction, MULI)
{
  const auto op = ConcuBinE::Instruction::create("MULI", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("MULI", op.symbol());
  ASSERT_EQ(Type::accu, op.type());
  ASSERT_EQ(0, op.arg());
}

// CMP =========================================================================

TEST(Instruction, CMP)
{
  const auto op = ConcuBinE::Instruction::create("CMP", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_TRUE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("CMP", op.symbol());
  ASSERT_EQ(Type::accu | Type::read, op.type());
  ASSERT_EQ(0, op.arg());
  ASSERT_FALSE(op.indirect());
}

// JMP =========================================================================

TEST(Instruction, JMP)
{
  const auto op = ConcuBinE::Instruction::create("JMP", word_max);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_TRUE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("JMP", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(word_max, op.arg());
}

// JZ ==========================================================================

TEST(Instruction, JZ)
{
  const auto op = ConcuBinE::Instruction::create("JZ", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_TRUE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("JZ", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(0, op.arg());
}

// JNZ =========================================================================

TEST(Instruction, JNZ)
{
  const auto op = ConcuBinE::Instruction::create("JNZ", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_TRUE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("JNZ", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(0, op.arg());
}

// JS ==========================================================================

TEST(Instruction, JS)
{
  const auto op = ConcuBinE::Instruction::create("JS", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_TRUE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("JS", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(0, op.arg());
}

// JNS =========================================================================

TEST(Instruction, JNS)
{
  const auto op = ConcuBinE::Instruction::create("JNS", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_TRUE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("JNS", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(0, op.arg());
}

// JNZNS =======================================================================

TEST(Instruction, JNZNS)
{
  const auto op = ConcuBinE::Instruction::create("JNZNS", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_TRUE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("JNZNS", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(0, op.arg());
}

// MEM =========================================================================

TEST(Instruction, MEM)
{
  const auto op = ConcuBinE::Instruction::create("MEM", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_TRUE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("MEM", op.symbol());
  ASSERT_EQ(Type::accu | Type::mem | Type::read, op.type());
  ASSERT_EQ(0, op.arg());
  ASSERT_FALSE(op.indirect());
}

// CAS =========================================================================

TEST(Instruction, CAS)
{
  const auto op = ConcuBinE::Instruction::create("CAS", 0);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_TRUE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_TRUE(op.requires_flush());

  ASSERT_EQ("CAS", op.symbol());
  ASSERT_EQ(
    Type::accu | Type::read | Type::atomic | Type::barrier,
    op.type());
  ASSERT_EQ(0, op.arg());
  ASSERT_FALSE(op.indirect());
}

// CHECK =======================================================================

TEST(Instruction, CHECK)
{
  const auto op = ConcuBinE::Instruction::create("CHECK", 1);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("CHECK", op.symbol());
  ASSERT_EQ(Type::none, op.type());
  ASSERT_EQ(1, op.arg());
}

// HALT ========================================================================

TEST(Instruction, HALT)
{
  const auto op = ConcuBinE::Instruction::create("HALT");

  ASSERT_TRUE(op.is_nullary());
  ASSERT_FALSE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_TRUE(op.requires_flush());

  ASSERT_EQ("HALT", op.symbol());
  ASSERT_EQ(Type::barrier | Type::control, op.type());
}

// EXIT ========================================================================

TEST(Instruction, EXIT)
{
  const auto op = ConcuBinE::Instruction::create("EXIT", 1);

  ASSERT_TRUE(op.is_nullary());
  ASSERT_TRUE(op.is_unary());
  ASSERT_FALSE(op.is_memory());
  ASSERT_FALSE(op.is_jump());
  ASSERT_FALSE(op.requires_flush());

  ASSERT_EQ("EXIT", op.symbol());
  ASSERT_EQ(Type::control, op.type());
  ASSERT_EQ(1, op.arg());
}

} // namespace ConcuBinE::test
