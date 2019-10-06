#include <gtest/gtest.h>

#include "publicate.hh"

#include "instruction.hh"

#include "program.hh"

namespace ConcuBinE::test {

//==============================================================================
// Instruction tests
//==============================================================================

struct Instruction : public ::testing::Test
{
  using Type = ConcuBinE::Instruction::Type;

  ConcuBinE::Instruction instruction;
  Program program;
};

// construction ================================================================

TEST_F(Instruction, construction)
{
  ConcuBinE::Instruction op1 (ConcuBinE::Instruction::create("LOAD", 1, true));
  ConcuBinE::Instruction::Concept * base = op1.model.get();

  // copy construction
  ConcuBinE::Instruction op2 (op1);
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_NE(op1.model.get(), op2.model.get());

  // move construction
  ConcuBinE::Instruction op3 (std::move(op1));
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

TEST_F(Instruction, create)
{
  // normal
  instruction = ConcuBinE::Instruction::create("EXIT", 0);

  ASSERT_EQ("EXIT", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(0, instruction.arg());

  // negative arg
  instruction = ConcuBinE::Instruction::create("LOAD", static_cast<word_t>(-1));

  ASSERT_EQ("LOAD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(word_max, instruction.arg());

  // arg overflow
  instruction = ConcuBinE::Instruction::create("LOAD", word_t(word_max + 1));

  ASSERT_EQ("LOAD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());

  // unknown instruction
  try { instruction = ConcuBinE::Instruction::create("NOP"); } catch (...) {}
  try { instruction = ConcuBinE::Instruction::create("NOP", 0); } catch (...) {}
}

// Instruction::contains =======================================================

TEST_F(Instruction, contains)
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

TEST_F(Instruction, type)
{
  instruction = ConcuBinE::Instruction::create("EXIT", 0);

  ASSERT_EQ(Type::control, instruction.type());

  instruction.type(Type::none);
  ASSERT_EQ(Type::none, instruction.type());
}

// Instruction::arg ============================================================

TEST_F(Instruction, arg)
{
  instruction = ConcuBinE::Instruction::create("EXIT", 1);

  ASSERT_EQ(1, instruction.arg());

  instruction.arg(0);
  ASSERT_EQ(0, instruction.arg());
}

// Instruction::indirect =======================================================

TEST_F(Instruction, indirect)
{
  instruction = ConcuBinE::Instruction::create("LOAD", 0);

  ASSERT_FALSE(instruction.indirect());

  instruction.indirect(true);
  ASSERT_TRUE(instruction.indirect());
}

// operators ===================================================================

TEST_F(Instruction, operator_equals)
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

TEST_F(Instruction, LOAD)
{
  instruction = ConcuBinE::Instruction::create("LOAD", 0);

  ASSERT_EQ("LOAD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());
}

// STORE =======================================================================

TEST_F(Instruction, STORE)
{
  instruction = ConcuBinE::Instruction::create("STORE", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_TRUE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_TRUE(instruction.requires_flush());

  ASSERT_EQ("STORE", instruction.symbol());
  ASSERT_EQ(Type::write, instruction.type());
  ASSERT_EQ(0, instruction.arg());
  ASSERT_FALSE(instruction.indirect());
}

// FENCE =======================================================================

TEST_F(Instruction, FENCE)
{
  instruction = ConcuBinE::Instruction::create("FENCE");

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_FALSE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_TRUE(instruction.requires_flush());

  ASSERT_EQ("FENCE", instruction.symbol());
  ASSERT_EQ(Type::barrier, instruction.type());
}

// ADD =========================================================================

TEST_F(Instruction, ADD)
{
  instruction = ConcuBinE::Instruction::create("ADD", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_TRUE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("ADD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());
  ASSERT_FALSE(instruction.indirect());
}

// ADDI ========================================================================

TEST_F(Instruction, ADDI)
{
  instruction = ConcuBinE::Instruction::create("ADDI", 1);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("ADDI", instruction.symbol());
  ASSERT_EQ(Type::accu, instruction.type());
  ASSERT_EQ(1, instruction.arg());
}

// SUB =========================================================================

TEST_F(Instruction, SUB)
{
  instruction = ConcuBinE::Instruction::create("SUB", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_TRUE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("SUB", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());
  ASSERT_FALSE(instruction.indirect());
}

// SUBI ========================================================================

TEST_F(Instruction, SUBI)
{
  instruction = ConcuBinE::Instruction::create("SUBI", 1);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("SUBI", instruction.symbol());
  ASSERT_EQ(Type::accu, instruction.type());
  ASSERT_EQ(1, instruction.arg());
}

// MUL =========================================================================

TEST_F(Instruction, MUL)
{
  instruction = ConcuBinE::Instruction::create("MUL", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_TRUE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("MUL", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());
  ASSERT_FALSE(instruction.indirect());
}

// MULI ========================================================================

TEST_F(Instruction, MULI)
{
  instruction = ConcuBinE::Instruction::create("MULI", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("MULI", instruction.symbol());
  ASSERT_EQ(Type::accu, instruction.type());
  ASSERT_EQ(0, instruction.arg());
}

// CMP =========================================================================

TEST_F(Instruction, CMP)
{
  instruction = ConcuBinE::Instruction::create("CMP", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_TRUE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("CMP", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());
  ASSERT_FALSE(instruction.indirect());
}

// JMP =========================================================================

TEST_F(Instruction, JMP)
{
  instruction = ConcuBinE::Instruction::create("JMP", word_max);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_TRUE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("JMP", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(word_max, instruction.arg());
}

// JZ ==========================================================================

TEST_F(Instruction, JZ)
{
  instruction = ConcuBinE::Instruction::create("JZ", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_TRUE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("JZ", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(0, instruction.arg());
}

// JNZ =========================================================================

TEST_F(Instruction, JNZ)
{
  instruction = ConcuBinE::Instruction::create("JNZ", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_TRUE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("JNZ", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(0, instruction.arg());
}

// JS ==========================================================================

TEST_F(Instruction, JS)
{
  instruction = ConcuBinE::Instruction::create("JS", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_TRUE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("JS", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(0, instruction.arg());
}

// JNS =========================================================================

TEST_F(Instruction, JNS)
{
  instruction = ConcuBinE::Instruction::create("JNS", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_TRUE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("JNS", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(0, instruction.arg());
}

// JNZNS =======================================================================

TEST_F(Instruction, JNZNS)
{
  instruction = ConcuBinE::Instruction::create("JNZNS", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_TRUE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("JNZNS", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(0, instruction.arg());
}

// MEM =========================================================================

TEST_F(Instruction, MEM)
{
  instruction = ConcuBinE::Instruction::create("MEM", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_TRUE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("MEM", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::mem | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());
  ASSERT_FALSE(instruction.indirect());
}

// CAS =========================================================================

TEST_F(Instruction, CAS)
{
  instruction = ConcuBinE::Instruction::create("CAS", 0);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_TRUE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_TRUE(instruction.requires_flush());

  ASSERT_EQ("CAS", instruction.symbol());
  ASSERT_EQ(
    Type::accu | Type::read | Type::atomic | Type::barrier,
    instruction.type());
  ASSERT_EQ(0, instruction.arg());
  ASSERT_FALSE(instruction.indirect());
}

// CHECK =======================================================================

TEST_F(Instruction, CHECK)
{
  instruction = ConcuBinE::Instruction::create("CHECK", 1);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("CHECK", instruction.symbol());
  ASSERT_EQ(Type::none, instruction.type());
  ASSERT_EQ(1, instruction.arg());
}

// HALT ========================================================================

TEST_F(Instruction, HALT)
{
  instruction = ConcuBinE::Instruction::create("HALT");

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_FALSE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_TRUE(instruction.requires_flush());

  ASSERT_EQ("HALT", instruction.symbol());
  ASSERT_EQ(Type::barrier | Type::control, instruction.type());
}

// EXIT ========================================================================

TEST_F(Instruction, EXIT)
{
  instruction = ConcuBinE::Instruction::create("EXIT", 1);

  ASSERT_TRUE(instruction.is_nullary());
  ASSERT_TRUE(instruction.is_unary());
  ASSERT_FALSE(instruction.is_memory());
  ASSERT_FALSE(instruction.is_jump());
  ASSERT_FALSE(instruction.requires_flush());

  ASSERT_EQ("EXIT", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(1, instruction.arg());
}

} // namespace ConcuBinE::test
