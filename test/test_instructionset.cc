#include <gtest/gtest.h>

#include "program.hh"
#include "machine.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct InstructionSetTest : public ::testing::Test
{
  Program         program;
  Thread          thread;
  Machine         machine;
  InstructionPtr  instruction;

  InstructionSetTest () : thread(machine, 0, program) {};
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

  machine.memory[0] = 1;

  ASSERT_EQ("LOAD", instruction->get_symbol());

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, machine.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, machine.memory[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);
}

/* STORE **********************************************************************/
TEST_F(InstructionSetTest, STORE)
{
  instruction = Instruction::Set::create("STORE", 0);

  ASSERT_EQ("STORE", instruction->get_symbol());

  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, machine.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, machine.memory[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);
}

/* ADD ************************************************************************/
TEST_F(InstructionSetTest, ADD)
{
  instruction = Instruction::Set::create("ADD", 0);

  ASSERT_EQ("ADD", instruction->get_symbol());

  machine.memory[0] = 1;

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, machine.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, machine.memory[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);
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
}

/* SUB ************************************************************************/
TEST_F(InstructionSetTest, SUB)
{
  instruction = Instruction::Set::create("SUB", 0);

  ASSERT_EQ("SUB", instruction->get_symbol());

  thread.accu = 1;
  machine.memory[0] = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, machine.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, machine.memory[0]);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);
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
}

/* CMP ************************************************************************/
TEST_F(InstructionSetTest, CMP)
{
  instruction = Instruction::Set::create("CMP", 0);

  ASSERT_EQ("CMP", instruction->get_symbol());

  /* true */
  thread.accu = 1;
  machine.memory[0] = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, machine.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, machine.memory[0]);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* false */
  instruction->execute(thread);

  ASSERT_EQ(1, machine.memory[0]);
  ASSERT_EQ(word_max, thread.accu);
  ASSERT_EQ(2, thread.pc);
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
}

/* MEM ************************************************************************/
TEST_F(InstructionSetTest, MEM)
{
  instruction = Instruction::Set::create("MEM", 0);

  ASSERT_EQ("MEM", instruction->get_symbol());

  machine.memory[0] = 1;

  ASSERT_EQ(0, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, machine.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, machine.memory[0]);
}

/* CAS ************************************************************************/
TEST_F(InstructionSetTest, CAS)
{
  instruction = Instruction::Set::create("CAS", 0);

  ASSERT_EQ("CAS", instruction->get_symbol());

  /* success */
  thread.mem = 1;
  thread.accu = 0;
  machine.memory[0] = 1;

  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, machine.memory[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, machine.memory[0]);

  /* fail */
  instruction->execute(thread);

  ASSERT_EQ(2, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(0, machine.memory[0]);
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
}
