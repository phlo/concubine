#include <gtest/gtest.h>

#include "instructionset.hh"

#include "program.hh"
#include "simulator.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct InstructionSetTest : public ::testing::Test
{
  using Type = Instruction::Type;
  using Types = Instruction::Types;

  Instruction_ptr   instruction;
  Program           program;
  Simulator         simulator;
  Thread            thread = Thread(simulator, 0, program);
};

/* Instruction::Set::create (factory) *****************************************/
TEST_F(InstructionSetTest, factory)
{
  /* normal */
  instruction = Instruction::Set::create("EXIT", 0);

  ASSERT_EQ("EXIT", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());
  ASSERT_EQ(0, dynamic_pointer_cast<Unary>(instruction)->arg);

  /* negative arg */
  instruction = Instruction::Set::create("LOAD", static_cast<word_t>(-1));

  ASSERT_EQ("LOAD", instruction->symbol());
  ASSERT_EQ(Types::accu | Types::read, instruction->type());
  ASSERT_EQ(word_max, dynamic_pointer_cast<Unary>(instruction)->arg);

  /* arg overflow */
  instruction = Instruction::Set::create("LOAD", word_t(word_max + 1));

  ASSERT_EQ("LOAD", instruction->symbol());
  ASSERT_EQ(Types::accu | Types::read, instruction->type());
  ASSERT_EQ(0, dynamic_pointer_cast<Unary>(instruction)->arg);

  /* unknown instruction */
  try { instruction = Instruction::Set::create("NOP"); } catch (...) {}
  try { instruction = Instruction::Set::create("NOP", 0); } catch (...) {}
}

/* InstructionSet::contains (std::string) *************************************/
TEST_F(InstructionSetTest, contains)
{
  ASSERT_EQ(true, Instruction::Set::contains("LOAD"));
  ASSERT_EQ(true, Instruction::Set::contains("STORE"));
  ASSERT_EQ(true, Instruction::Set::contains("FENCE"));
  ASSERT_EQ(true, Instruction::Set::contains("ADD"));
  ASSERT_EQ(true, Instruction::Set::contains("ADDI"));
  ASSERT_EQ(true, Instruction::Set::contains("SUB"));
  ASSERT_EQ(true, Instruction::Set::contains("SUBI"));
  ASSERT_EQ(true, Instruction::Set::contains("CMP"));
  ASSERT_EQ(true, Instruction::Set::contains("JMP"));
  ASSERT_EQ(true, Instruction::Set::contains("JZ"));
  ASSERT_EQ(true, Instruction::Set::contains("JNZ"));
  ASSERT_EQ(true, Instruction::Set::contains("JS"));
  ASSERT_EQ(true, Instruction::Set::contains("JNS"));
  ASSERT_EQ(true, Instruction::Set::contains("JNZNS"));
  ASSERT_EQ(true, Instruction::Set::contains("MEM"));
  ASSERT_EQ(true, Instruction::Set::contains("CAS"));
  ASSERT_EQ(true, Instruction::Set::contains("CHECK"));
  ASSERT_EQ(true, Instruction::Set::contains("HALT"));
  ASSERT_EQ(true, Instruction::Set::contains("EXIT"));

  ASSERT_EQ(false, Instruction::Set::contains("NOP"));
}

/* operators ******************************************************************/
TEST_F(InstructionSetTest, operator_equals)
{
  /* Nullary */
  ASSERT_EQ(
    *Instruction::Set::create("FENCE"),
    *Instruction::Set::create("FENCE"));

  ASSERT_NE(
    *Instruction::Set::create("FENCE"),
    *Instruction::Set::create("HALT"));

  /* Unary */
  ASSERT_EQ(
    *Instruction::Set::create("ADDI", 1),
    *Instruction::Set::create("ADDI", 1));

  ASSERT_NE(
    *Instruction::Set::create("ADDI", 1),
    *Instruction::Set::create("ADDI", 2));

  ASSERT_NE(
    *Instruction::Set::create("ADDI", 1),
    *Instruction::Set::create("SUBI", 1));

  /* Memory */
  ASSERT_EQ(
    *Instruction::Set::create("STORE", 1),
    *Instruction::Set::create("STORE", 1));

  ASSERT_NE(
    *Instruction::Set::create("STORE", 1),
    *Instruction::Set::create("STORE", 2));

  ASSERT_NE(
    *Instruction::Set::create("STORE", 1, true),
    *Instruction::Set::create("STORE", 1, false));

  ASSERT_NE(
    *Instruction::Set::create("STORE", 1),
    *Instruction::Set::create("LOAD", 1));
}

/* LOAD ***********************************************************************/
TEST_F(InstructionSetTest, LOAD)
{
  instruction = Instruction::Set::create("LOAD", 0);

  simulator.heap[0] = 1;

  ASSERT_EQ("LOAD", instruction->symbol());
  ASSERT_EQ(Types::accu | Types::read, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

/* STORE **********************************************************************/
TEST_F(InstructionSetTest, STORE)
{
  instruction = Instruction::Set::create("STORE", 0);

  ASSERT_EQ("STORE", instruction->symbol());
  ASSERT_EQ(Types::write, instruction->type());

  thread.accu = 1;

  ASSERT_EQ(0, thread.pc);

  ASSERT_FALSE(thread.buffer.full);
  ASSERT_EQ(0, thread.buffer.address);
  ASSERT_EQ(0, thread.buffer.value);

  ASSERT_EQ(0, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  ASSERT_TRUE(thread.buffer.full);
  ASSERT_EQ(0, thread.buffer.address);
  ASSERT_EQ(1, thread.buffer.value);

  ASSERT_EQ(0, simulator.heap[0]);
}

/* FENCE **********************************************************************/
TEST_F(InstructionSetTest, FENCE)
{
  instruction = Instruction::Set::create("FENCE");

  ASSERT_EQ("FENCE", instruction->symbol());
  ASSERT_EQ(Types::barrier, instruction->type());

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
}

/* ADD ************************************************************************/
TEST_F(InstructionSetTest, ADD)
{
  instruction = Instruction::Set::create("ADD", 0);

  ASSERT_EQ("ADD", instruction->symbol());
  ASSERT_EQ(Types::accu | Types::read, instruction->type());

  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

/* ADDI ***********************************************************************/
TEST_F(InstructionSetTest, ADDI)
{
  instruction = Instruction::Set::create("ADDI", 1);

  ASSERT_EQ("ADDI", instruction->symbol());
  ASSERT_EQ(Types::accu, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
}

/* SUB ************************************************************************/
TEST_F(InstructionSetTest, SUB)
{
  instruction = Instruction::Set::create("SUB", 0);

  ASSERT_EQ("SUB", instruction->symbol());
  ASSERT_EQ(Types::accu | Types::read, instruction->type());

  thread.accu = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

/* SUBI ***********************************************************************/
TEST_F(InstructionSetTest, SUBI)
{
  instruction = Instruction::Set::create("SUBI", 1);

  ASSERT_EQ("SUBI", instruction->symbol());
  ASSERT_EQ(Types::accu, instruction->type());

  thread.accu = 1;

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(0, thread.accu);
}

/* CMP ************************************************************************/
TEST_F(InstructionSetTest, CMP)
{
  instruction = Instruction::Set::create("CMP", 0);

  ASSERT_EQ("CMP", instruction->symbol());
  ASSERT_EQ(Types::accu | Types::read, instruction->type());

  thread.accu = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(2, thread.pc);
  ASSERT_EQ(word_max, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);
}

/* JMP ************************************************************************/
TEST_F(InstructionSetTest, JMP)
{
  instruction = Instruction::Set::create("JMP", word_max);

  ASSERT_EQ("JMP", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(word_max, thread.pc);

  instruction = Instruction::Set::create("JMP", 0);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);
}

/* JZ *************************************************************************/
TEST_F(InstructionSetTest, JZ)
{
  instruction = Instruction::Set::create("JZ", 0);

  ASSERT_EQ("JZ", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  thread.accu = 1;

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
}

/* JNZ ************************************************************************/
TEST_F(InstructionSetTest, JNZ)
{
  instruction = Instruction::Set::create("JNZ", 0);

  ASSERT_EQ("JNZ", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  thread.accu = 1;

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);
}

/* JS *************************************************************************/
TEST_F(InstructionSetTest, JS)
{
  instruction = Instruction::Set::create("JS", 0);

  ASSERT_EQ("JS", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  thread.accu = word_max;

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);
}

/* JNS ************************************************************************/
TEST_F(InstructionSetTest, JNS)
{
  instruction = Instruction::Set::create("JNS", 0);

  ASSERT_EQ("JNS", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  thread.accu = word_max;

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
}

/* JNZNS **********************************************************************/
TEST_F(InstructionSetTest, JNZNS)
{
  instruction = Instruction::Set::create("JNZNS", 0);

  ASSERT_EQ("JNZNS", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);

  thread.accu = word_max;

  instruction->execute(thread);

  ASSERT_EQ(2, thread.pc);

  thread.accu = 1;

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);
}

/* MEM ************************************************************************/
TEST_F(InstructionSetTest, MEM)
{
  instruction = Instruction::Set::create("MEM", 0);

  ASSERT_EQ("MEM", instruction->symbol());
  ASSERT_EQ(Types::accu | Types::mem | Types::read, instruction->type());

  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(0, thread.mem);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, simulator.heap[0]);
}

/* CAS ************************************************************************/
TEST_F(InstructionSetTest, CAS)
{
  instruction = Instruction::Set::create("CAS", 0);

  ASSERT_EQ("CAS", instruction->symbol());
  ASSERT_EQ(
    Types::accu | Types::read | Types::atomic | Types::barrier,
    instruction->type());

  thread.accu = 0;
  thread.mem = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(2, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(0, simulator.heap[0]);
}

/* CHECK **********************************************************************/
TEST_F(InstructionSetTest, CHECK)
{
  instruction = Instruction::Set::create("CHECK", 1);

  ASSERT_EQ("CHECK", instruction->symbol());
  ASSERT_EQ(Types::barrier | Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.check);
  ASSERT_EQ(Thread::State::initial, thread.state);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.check);
  ASSERT_EQ(Thread::State::waiting, thread.state);
}

/* HALT ***********************************************************************/
TEST_F(InstructionSetTest, HALT)
{
  // TODO
  instruction = Instruction::Set::create("HALT");

  ASSERT_EQ("HALT", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());
}

/* EXIT ***********************************************************************/
TEST_F(InstructionSetTest, EXIT)
{
  instruction = Instruction::Set::create("EXIT", 1);

  ASSERT_EQ("EXIT", instruction->symbol());
  ASSERT_EQ(Types::control, instruction->type());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(Thread::State::initial, thread.state);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(Thread::State::exited, thread.state);
}
