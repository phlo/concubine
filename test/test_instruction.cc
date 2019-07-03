#include <gtest/gtest.h>

#include "instruction.hh"

#include "program.hh"
#include "simulator.hh"

namespace test {

//==============================================================================
// Instruction tests
//==============================================================================

struct Instruction : public ::testing::Test
{
  using Type = ::Instruction::Type;

  ::Instruction instruction;
  Program program;
  Simulator simulator = Simulator(std::make_shared<Program::List>(1));
  Thread thread = Thread(simulator, 0, program);

  Instruction ()
    {
      simulator.schedule = std::make_unique<Schedule>(simulator.programs);
    }
};

// construction ================================================================

TEST_F(Instruction, construction)
{
  ::Instruction op1 (::Instruction::create("LOAD", 1, true));
  ::Instruction::Concept * base = op1.model.get();

  // copy construction
  ::Instruction op2 (op1);
  ASSERT_TRUE(op1.model);
  ASSERT_TRUE(op2.model);
  ASSERT_NE(op1.model.get(), op2.model.get());

  // move construction
  ::Instruction op3 (std::move(op1));
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
  instruction = ::Instruction::create("EXIT", 0);

  ASSERT_EQ("EXIT", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
  ASSERT_EQ(0, instruction.arg());

  // negative arg
  instruction = ::Instruction::create("LOAD", static_cast<word_t>(-1));

  ASSERT_EQ("LOAD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(word_max, instruction.arg());

  // arg overflow
  instruction = ::Instruction::create("LOAD", word_t(word_max + 1));

  ASSERT_EQ("LOAD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());
  ASSERT_EQ(0, instruction.arg());

  // unknown instruction
  try { instruction = ::Instruction::create("NOP"); } catch (...) {}
  try { instruction = ::Instruction::create("NOP", 0); } catch (...) {}
}

// Instruction::contains =======================================================

TEST_F(Instruction, contains)
{
  ASSERT_EQ(true, ::Instruction::contains("LOAD"));
  ASSERT_EQ(true, ::Instruction::contains("STORE"));
  ASSERT_EQ(true, ::Instruction::contains("FENCE"));
  ASSERT_EQ(true, ::Instruction::contains("ADD"));
  ASSERT_EQ(true, ::Instruction::contains("ADDI"));
  ASSERT_EQ(true, ::Instruction::contains("SUB"));
  ASSERT_EQ(true, ::Instruction::contains("SUBI"));
  ASSERT_EQ(true, ::Instruction::contains("CMP"));
  ASSERT_EQ(true, ::Instruction::contains("JMP"));
  ASSERT_EQ(true, ::Instruction::contains("JZ"));
  ASSERT_EQ(true, ::Instruction::contains("JNZ"));
  ASSERT_EQ(true, ::Instruction::contains("JS"));
  ASSERT_EQ(true, ::Instruction::contains("JNS"));
  ASSERT_EQ(true, ::Instruction::contains("JNZNS"));
  ASSERT_EQ(true, ::Instruction::contains("MEM"));
  ASSERT_EQ(true, ::Instruction::contains("CAS"));
  ASSERT_EQ(true, ::Instruction::contains("CHECK"));
  ASSERT_EQ(true, ::Instruction::contains("HALT"));
  ASSERT_EQ(true, ::Instruction::contains("EXIT"));

  ASSERT_EQ(false, ::Instruction::contains("NOP"));
}

// operators ===================================================================

TEST_F(Instruction, operator_equals)
{
  // Nullary
  ASSERT_EQ(
    ::Instruction::create("FENCE"),
    ::Instruction::create("FENCE"));

  ASSERT_NE(
    ::Instruction::create("FENCE"),
    ::Instruction::create("HALT"));

  // Unary
  ASSERT_EQ(
    ::Instruction::create("ADDI", 1),
    ::Instruction::create("ADDI", 1));

  ASSERT_NE(
    ::Instruction::create("ADDI", 1),
    ::Instruction::create("ADDI", 2));

  ASSERT_NE(
    ::Instruction::create("ADDI", 1),
    ::Instruction::create("SUBI", 1));

  // Memory
  ASSERT_EQ(
    ::Instruction::create("STORE", 1),
    ::Instruction::create("STORE", 1));

  ASSERT_NE(
    ::Instruction::create("STORE", 1),
    ::Instruction::create("STORE", 2));

  ASSERT_NE(
    ::Instruction::create("STORE", 1, true),
    ::Instruction::create("STORE", 1, false));

  ASSERT_NE(
    ::Instruction::create("STORE", 1),
    ::Instruction::create("LOAD", 1));
}

// LOAD ========================================================================

TEST_F(Instruction, LOAD)
{
  instruction = ::Instruction::create("LOAD", 0);

  simulator.heap[0] = 1;

  ASSERT_EQ("LOAD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

// STORE =======================================================================

TEST_F(Instruction, STORE)
{
  instruction = ::Instruction::create("STORE", 0);

  ASSERT_EQ("STORE", instruction.symbol());
  ASSERT_EQ(Type::write, instruction.type());

  thread.accu = 1;

  ASSERT_EQ(0, thread.pc);

  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(0, thread.buffer.address);
  ASSERT_EQ(0, thread.buffer.value);

  ASSERT_EQ(0, simulator.heap[0]);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);

  ASSERT_TRUE(thread.buffer.full);
  ASSERT_EQ(0, thread.buffer.address);
  ASSERT_EQ(1, thread.buffer.value);

  ASSERT_EQ(0, simulator.heap[0]);
}

// FENCE =======================================================================

TEST_F(Instruction, FENCE)
{
  instruction = ::Instruction::create("FENCE");

  ASSERT_EQ("FENCE", instruction.symbol());
  ASSERT_EQ(Type::barrier, instruction.type());

  ASSERT_EQ(0, thread.pc);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
}

// ADD =========================================================================

TEST_F(Instruction, ADD)
{
  instruction = ::Instruction::create("ADD", 0);

  ASSERT_EQ("ADD", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());

  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

// ADDI ========================================================================

TEST_F(Instruction, ADDI)
{
  instruction = ::Instruction::create("ADDI", 1);

  ASSERT_EQ("ADDI", instruction.symbol());
  ASSERT_EQ(Type::accu, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
}

// SUB =========================================================================

TEST_F(Instruction, SUB)
{
  instruction = ::Instruction::create("SUB", 0);

  ASSERT_EQ("SUB", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());

  thread.accu = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

// SUBI ========================================================================

TEST_F(Instruction, SUBI)
{
  instruction = ::Instruction::create("SUBI", 1);

  ASSERT_EQ("SUBI", instruction.symbol());
  ASSERT_EQ(Type::accu, instruction.type());

  thread.accu = 1;

  ASSERT_EQ(0, thread.pc);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(0, thread.accu);
}

// CMP =========================================================================

TEST_F(Instruction, CMP)
{
  instruction = ::Instruction::create("CMP", 0);

  ASSERT_EQ("CMP", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::read, instruction.type());

  thread.accu = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction.execute(thread);

  ASSERT_EQ(2, thread.pc);
  ASSERT_EQ(word_max, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

// JMP =========================================================================

TEST_F(Instruction, JMP)
{
  instruction = ::Instruction::create("JMP", word_max);

  ASSERT_EQ("JMP", instruction.symbol());
  ASSERT_EQ(Type::control | Type::jump, instruction.type());

  ASSERT_EQ(0, thread.pc);

  instruction.execute(thread);

  ASSERT_EQ(word_max, thread.pc);

  instruction = ::Instruction::create("JMP", 0);

  instruction.execute(thread);

  ASSERT_EQ(0, thread.pc);
}

// JZ ==========================================================================

TEST_F(Instruction, JZ)
{
  instruction = ::Instruction::create("JZ", 0);

  ASSERT_EQ("JZ", instruction.symbol());
  ASSERT_EQ(Type::control | Type::jump, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(0, thread.pc);

  thread.accu = 1;

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
}

// JNZ =========================================================================

TEST_F(Instruction, JNZ)
{
  instruction = ::Instruction::create("JNZ", 0);

  ASSERT_EQ("JNZ", instruction.symbol());
  ASSERT_EQ(Type::control | Type::jump, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);

  thread.accu = 1;

  instruction.execute(thread);

  ASSERT_EQ(0, thread.pc);
}

// JS ==========================================================================

TEST_F(Instruction, JS)
{
  instruction = ::Instruction::create("JS", 0);

  ASSERT_EQ("JS", instruction.symbol());
  ASSERT_EQ(Type::control | Type::jump, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);

  thread.accu = word_max;

  instruction.execute(thread);

  ASSERT_EQ(0, thread.pc);
}

// JNS =========================================================================

TEST_F(Instruction, JNS)
{
  instruction = ::Instruction::create("JNS", 0);

  ASSERT_EQ("JNS", instruction.symbol());
  ASSERT_EQ(Type::control | Type::jump, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(0, thread.pc);

  thread.accu = word_max;

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
}

// JNZNS =======================================================================

TEST_F(Instruction, JNZNS)
{
  instruction = ::Instruction::create("JNZNS", 0);

  ASSERT_EQ("JNZNS", instruction.symbol());
  ASSERT_EQ(Type::control | Type::jump, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);

  thread.accu = word_max;

  instruction.execute(thread);

  ASSERT_EQ(2, thread.pc);

  thread.accu = 1;

  instruction.execute(thread);

  ASSERT_EQ(0, thread.pc);
}

// MEM =========================================================================

TEST_F(Instruction, MEM)
{
  instruction = ::Instruction::create("MEM", 0);

  ASSERT_EQ("MEM", instruction.symbol());
  ASSERT_EQ(Type::accu | Type::mem | Type::read, instruction.type());

  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(0, thread.mem);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, simulator.heap[0]);
}

// CAS =========================================================================

TEST_F(Instruction, CAS)
{
  instruction = ::Instruction::create("CAS", 0);

  ASSERT_EQ("CAS", instruction.symbol());
  ASSERT_EQ(
    Type::accu | Type::read | Type::atomic | Type::barrier,
    instruction.type());

  thread.accu = 0;
  thread.mem = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, simulator.heap[0]);

  instruction.execute(thread);

  ASSERT_EQ(2, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(0, simulator.heap[0]);
}

// CHECK =======================================================================

TEST_F(Instruction, CHECK)
{
  instruction = ::Instruction::create("CHECK", 1);

  ASSERT_EQ("CHECK", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.check);
  ASSERT_EQ(Thread::State::initial, thread.state);

  instruction.execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.check);
  ASSERT_EQ(Thread::State::waiting, thread.state);
}

// HALT ========================================================================

TEST_F(Instruction, HALT)
{
  // TODO
  instruction = ::Instruction::create("HALT");

  ASSERT_EQ("HALT", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());
}

// EXIT ========================================================================

TEST_F(Instruction, EXIT)
{
  instruction = ::Instruction::create("EXIT", 1);

  ASSERT_EQ("EXIT", instruction.symbol());
  ASSERT_EQ(Type::control, instruction.type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(Thread::State::initial, thread.state);

  instruction.execute(thread);

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(Thread::State::exited, thread.state);
}

} // namespace test
