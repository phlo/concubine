#include <gtest/gtest.h>

#include "program.hh"
#include "simulator.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct InstructionSetTest : public ::testing::Test
{
  InstructionPtr  instruction;
  ProgramPtr      program;
  Simulator       simulator;
  Thread          thread = Thread(simulator, 0, program);
};

/* Instruction::Set::create (Factory) *****************************************/
TEST_F(InstructionSetTest, Factory)
{
  /* normal */
  instruction = Instruction::Set::create("EXIT", 0);

  ASSERT_EQ("EXIT", instruction->get_symbol());
  ASSERT_EQ(Instruction::Type::UNARY, instruction->get_type());
  ASSERT_EQ(0, dynamic_pointer_cast<UnaryInstruction>(instruction)->arg);

  /* negative arg */
  instruction = Instruction::Set::create("LOAD", static_cast<word>(-1));

  ASSERT_EQ("LOAD", instruction->get_symbol());
  ASSERT_EQ(Instruction::Type::UNARY, instruction->get_type());
  ASSERT_EQ(word_max, dynamic_pointer_cast<UnaryInstruction>(instruction)->arg);

  /* arg overflow */
  instruction = Instruction::Set::create("LOAD", word(word_max + 1));

  ASSERT_EQ("LOAD", instruction->get_symbol());
  ASSERT_EQ(Instruction::Type::UNARY, instruction->get_type());
  ASSERT_EQ(0, dynamic_pointer_cast<UnaryInstruction>(instruction)->arg);

  /* unknown instruction */
  try { instruction = Instruction::Set::create("NOP"); } catch (...) {}
  try { instruction = Instruction::Set::create("NOP", 0); } catch (...) {}
}

/* LOAD ***********************************************************************/
TEST_F(InstructionSetTest, LOAD)
{
  instruction = Instruction::Set::create("LOAD", 0);

  simulator.memory[0] = 1;

  ASSERT_EQ("LOAD", instruction->get_symbol());

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.memory[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU,
    instruction->get_attributes());
}

/* STORE **********************************************************************/
TEST_F(InstructionSetTest, STORE)
{
  instruction = Instruction::Set::create("STORE", 0);

  ASSERT_EQ("STORE", instruction->get_symbol());

  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, simulator.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.memory[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_HEAP,
    instruction->get_attributes());
}

/* ADD ************************************************************************/
TEST_F(InstructionSetTest, ADD)
{
  instruction = Instruction::Set::create("ADD", 0);

  ASSERT_EQ("ADD", instruction->get_symbol());

  simulator.memory[0] = 1;

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.memory[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU,
    instruction->get_attributes());
}

/* ADDI ***********************************************************************/
TEST_F(InstructionSetTest, ADDI)
{
  instruction = Instruction::Set::create("ADDI", 1);

  ASSERT_EQ("ADDI", instruction->get_symbol());

  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU,
    instruction->get_attributes());
}

/* SUB ************************************************************************/
TEST_F(InstructionSetTest, SUB)
{
  instruction = Instruction::Set::create("SUB", 0);

  ASSERT_EQ("SUB", instruction->get_symbol());

  thread.accu = 1;
  simulator.memory[0] = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.memory[0]);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU,
    instruction->get_attributes());
}

/* SUBI ***********************************************************************/
TEST_F(InstructionSetTest, SUBI)
{
  instruction = Instruction::Set::create("SUBI", 1);

  ASSERT_EQ("SUBI", instruction->get_symbol());

  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU,
    instruction->get_attributes());
}

/* CMP ************************************************************************/
TEST_F(InstructionSetTest, CMP)
{
  instruction = Instruction::Set::create("CMP", 0);

  ASSERT_EQ("CMP", instruction->get_symbol());

  /* true */
  thread.accu = 1;
  simulator.memory[0] = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.memory[0]);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* false */
  instruction->execute(thread);

  ASSERT_EQ(1, simulator.memory[0]);
  ASSERT_EQ(word_max, thread.accu);
  ASSERT_EQ(2, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU,
    instruction->get_attributes());
}

/* JMP ************************************************************************/
TEST_F(InstructionSetTest, JMP)
{
  instruction = Instruction::Set::create("JMP", 0);

  ASSERT_EQ("JMP", instruction->get_symbol());

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  instruction = Instruction::Set::create("JMP", static_cast<word>(-1));

  instruction->execute(thread);

  ASSERT_EQ(word_max, thread.pc);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}

/* JZ *************************************************************************/
TEST_F(InstructionSetTest, JZ)
{
  instruction = Instruction::Set::create("JZ", 0);

  ASSERT_EQ("JZ", instruction->get_symbol());

  /* true */
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  /* false */
  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}

/* JNZ ************************************************************************/
TEST_F(InstructionSetTest, JNZ)
{
  instruction = Instruction::Set::create("JNZ", 0);

  ASSERT_EQ("JNZ", instruction->get_symbol());

  /* false */
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  /* true */
  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}

/* JS *************************************************************************/
TEST_F(InstructionSetTest, JS)
{
  instruction = Instruction::Set::create("JS", 0);

  ASSERT_EQ("JS", instruction->get_symbol());

  /* false */
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  /* true */
  thread.accu = static_cast<word>(-1);

  ASSERT_EQ(word_max, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}

/* JNS ************************************************************************/
TEST_F(InstructionSetTest, JNS)
{
  instruction = Instruction::Set::create("JNS", 0);

  ASSERT_EQ("JNS", instruction->get_symbol());

  /* true */
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  /* false */
  thread.accu = static_cast<word>(-1);

  ASSERT_EQ(word_max, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}

/* JNZNS **********************************************************************/
TEST_F(InstructionSetTest, JNZNS)
{
  instruction = Instruction::Set::create("JNZNS", 0);

  ASSERT_EQ("JNZNS", instruction->get_symbol());

  /* false => JZ */
  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  /* false => JS */
  thread.accu = static_cast<word>(-1);

  ASSERT_EQ(word_max, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(2, thread.pc);

  /* true */
  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}

/* MEM ************************************************************************/
TEST_F(InstructionSetTest, MEM)
{
  instruction = Instruction::Set::create("MEM", 0);

  ASSERT_EQ("MEM", instruction->get_symbol());

  simulator.memory[0] = 1;

  ASSERT_EQ(0, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.memory[0]);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU | Instruction::Attributes::ALTERS_MEM,
    instruction->get_attributes());
}

/* CAS ************************************************************************/
TEST_F(InstructionSetTest, CAS)
{
  instruction = Instruction::Set::create("CAS", 0);

  ASSERT_EQ("CAS", instruction->get_symbol());

  /* success */
  thread.mem = 1;
  thread.accu = 0;
  simulator.memory[0] = 1;

  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, simulator.memory[0]);

  /* fail */
  instruction->execute(thread);

  ASSERT_EQ(2, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(0, simulator.memory[0]);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::ALTERS_ACCU | Instruction::Attributes::ALTERS_HEAP,
    instruction->get_attributes());
}

/* SYNC ***********************************************************************/
TEST_F(InstructionSetTest, SYNC)
{
  instruction = Instruction::Set::create("SYNC", 1);

  ASSERT_EQ("SYNC", instruction->get_symbol());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.sync);
  ASSERT_EQ(Thread::State::INITIAL, thread.state);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.sync);
  ASSERT_EQ(Thread::State::WAITING, thread.state);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}

/* EXIT ***********************************************************************/
TEST_F(InstructionSetTest, EXIT)
{
  instruction = Instruction::Set::create("EXIT", 1);

  ASSERT_EQ("EXIT", instruction->get_symbol());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(Thread::State::INITIAL, thread.state);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(Thread::State::EXITING, thread.state);

  /* attributes */
  ASSERT_EQ(0, instruction->get_attributes());
}
