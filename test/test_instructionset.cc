#include <gtest/gtest.h>

#include "program.hh"
#include "simulator.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct InstructionSetTest : public ::testing::Test
{
  Instruction_ptr   instruction;
  Program           program;
  Simulator         simulator;
  Thread            thread = Thread(simulator, 0, program);
};

/* Instruction::Set::create (Factory) *****************************************/
TEST_F(InstructionSetTest, Factory)
{
  /* normal */
  instruction = Instruction::Set::create("EXIT", 0);

  ASSERT_EQ("EXIT", instruction->symbol());
  ASSERT_EQ(Instruction::Type::UNARY, instruction->type());
  ASSERT_EQ(0, dynamic_pointer_cast<Unary>(instruction)->arg);

  /* negative arg */
  instruction = Instruction::Set::create("LOAD", static_cast<word>(-1));

  ASSERT_EQ("LOAD", instruction->symbol());
  ASSERT_EQ(Instruction::Type::MEMORY, instruction->type());
  ASSERT_EQ(word_max, dynamic_pointer_cast<Unary>(instruction)->arg);

  /* arg overflow */
  instruction = Instruction::Set::create("LOAD", word(word_max + 1));

  ASSERT_EQ("LOAD", instruction->symbol());
  ASSERT_EQ(Instruction::Type::MEMORY, instruction->type());
  ASSERT_EQ(0, dynamic_pointer_cast<Unary>(instruction)->arg);

  /* unknown instruction */
  try { instruction = Instruction::Set::create("NOP"); } catch (...) {}
  try { instruction = Instruction::Set::create("NOP", 0); } catch (...) {}
}

/* InstructionSet::contains (std::string) *************************************/
TEST_F(InstructionSetTest, contains)
{
  ASSERT_EQ(Instruction::Type::MEMORY,  Instruction::Set::contains("LOAD"));
  ASSERT_EQ(Instruction::Type::MEMORY,  Instruction::Set::contains("STORE"));
  ASSERT_EQ(Instruction::Type::NULLARY, Instruction::Set::contains("FENCE"));
  ASSERT_EQ(Instruction::Type::MEMORY,  Instruction::Set::contains("ADD"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("ADDI"));
  ASSERT_EQ(Instruction::Type::MEMORY,  Instruction::Set::contains("SUB"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("SUBI"));
  ASSERT_EQ(Instruction::Type::MEMORY,  Instruction::Set::contains("CMP"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("JMP"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("JZ"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("JNZ"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("JS"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("JNS"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("JNZNS"));
  ASSERT_EQ(Instruction::Type::MEMORY,  Instruction::Set::contains("MEM"));
  ASSERT_EQ(Instruction::Type::MEMORY,  Instruction::Set::contains("CAS"));
  ASSERT_EQ(Instruction::Type::NULLARY, Instruction::Set::contains("CHECK"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("HALT"));
  ASSERT_EQ(Instruction::Type::UNARY,   Instruction::Set::contains("EXIT"));
}

/* operators ******************************************************************/
TEST_F(InstructionSetTest, operator_equals)
{
  /* UnaryInstruction */
  ASSERT_EQ(
    *Instruction::Set::create("ADDI", 1),
    *Instruction::Set::create("ADDI", 1));

  ASSERT_NE(
    *Instruction::Set::create("ADDI", 1),
    *Instruction::Set::create("ADDI", 2));

  ASSERT_NE(
    *Instruction::Set::create("ADDI", 1),
    *Instruction::Set::create("SUBI", 1));

  /* MemoryInstruction */
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

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu,
    instruction->attributes());
}

/* STORE **********************************************************************/
TEST_F(InstructionSetTest, STORE)
{
  instruction = Instruction::Set::create("STORE", 0);

  ASSERT_EQ("STORE", instruction->symbol());

  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::write,
    instruction->attributes());
}

/* ADD ************************************************************************/
TEST_F(InstructionSetTest, ADD)
{
  instruction = Instruction::Set::create("ADD", 0);

  ASSERT_EQ("ADD", instruction->symbol());

  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu,
    instruction->attributes());
}

/* ADDI ***********************************************************************/
TEST_F(InstructionSetTest, ADDI)
{
  instruction = Instruction::Set::create("ADDI", 1);

  ASSERT_EQ("ADDI", instruction->symbol());

  ASSERT_EQ(0, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu,
    instruction->attributes());
}

/* SUB ************************************************************************/
TEST_F(InstructionSetTest, SUB)
{
  instruction = Instruction::Set::create("SUB", 0);

  ASSERT_EQ("SUB", instruction->symbol());

  thread.accu = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu,
    instruction->attributes());
}

/* SUBI ***********************************************************************/
TEST_F(InstructionSetTest, SUBI)
{
  instruction = Instruction::Set::create("SUBI", 1);

  ASSERT_EQ("SUBI", instruction->symbol());

  thread.accu = 1;

  ASSERT_EQ(1, thread.accu);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu,
    instruction->attributes());
}

/* CMP ************************************************************************/
TEST_F(InstructionSetTest, CMP)
{
  instruction = Instruction::Set::create("CMP", 0);

  ASSERT_EQ("CMP", instruction->symbol());

  /* true */
  thread.accu = 1;
  simulator.heap[0] = 1;

  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, thread.pc);

  /* false */
  instruction->execute(thread);

  ASSERT_EQ(1, simulator.heap[0]);
  ASSERT_EQ(word_max, thread.accu);
  ASSERT_EQ(2, thread.pc);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu,
    instruction->attributes());
}

/* JMP ************************************************************************/
TEST_F(InstructionSetTest, JMP)
{
  instruction = Instruction::Set::create("JMP", 0);

  ASSERT_EQ("JMP", instruction->symbol());

  ASSERT_EQ(0, thread.pc);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);

  instruction = Instruction::Set::create("JMP", static_cast<word>(-1));

  instruction->execute(thread);

  ASSERT_EQ(word_max, thread.pc);

  /* attributes */
  ASSERT_EQ(0, instruction->attributes());
}

/* JZ *************************************************************************/
TEST_F(InstructionSetTest, JZ)
{
  instruction = Instruction::Set::create("JZ", 0);

  ASSERT_EQ("JZ", instruction->symbol());

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
  ASSERT_EQ(0, instruction->attributes());
}

/* JNZ ************************************************************************/
TEST_F(InstructionSetTest, JNZ)
{
  instruction = Instruction::Set::create("JNZ", 0);

  ASSERT_EQ("JNZ", instruction->symbol());

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
  ASSERT_EQ(0, instruction->attributes());
}

/* JS *************************************************************************/
TEST_F(InstructionSetTest, JS)
{
  instruction = Instruction::Set::create("JS", 0);

  ASSERT_EQ("JS", instruction->symbol());

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
  ASSERT_EQ(0, instruction->attributes());
}

/* JNS ************************************************************************/
TEST_F(InstructionSetTest, JNS)
{
  instruction = Instruction::Set::create("JNS", 0);

  ASSERT_EQ("JNS", instruction->symbol());

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
  ASSERT_EQ(0, instruction->attributes());
}

/* JNZNS **********************************************************************/
TEST_F(InstructionSetTest, JNZNS)
{
  instruction = Instruction::Set::create("JNZNS", 0);

  ASSERT_EQ("JNZNS", instruction->symbol());

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
  ASSERT_EQ(0, instruction->attributes());
}

/* MEM ************************************************************************/
TEST_F(InstructionSetTest, MEM)
{
  instruction = Instruction::Set::create("MEM", 0);

  ASSERT_EQ("MEM", instruction->symbol());

  simulator.heap[0] = 1;

  ASSERT_EQ(0, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu | Instruction::Attributes::mem,
    instruction->attributes());
}

/* CAS ************************************************************************/
TEST_F(InstructionSetTest, CAS)
{
  instruction = Instruction::Set::create("CAS", 0);

  ASSERT_EQ("CAS", instruction->symbol());

  /* success */
  thread.mem = 1;
  thread.accu = 0;
  simulator.heap[0] = 1;

  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(1, simulator.heap[0]);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(0, simulator.heap[0]);

  /* fail */
  instruction->execute(thread);

  ASSERT_EQ(2, thread.pc);
  ASSERT_EQ(1, thread.mem);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(0, simulator.heap[0]);

  /* attributes */
  ASSERT_EQ(
    Instruction::Attributes::accu | Instruction::Attributes::write,
    instruction->attributes());
}

/* SYNC ***********************************************************************/
TEST_F(InstructionSetTest, SYNC)
{
  instruction = Instruction::Set::create("SYNC", 1);

  ASSERT_EQ("SYNC", instruction->symbol());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.sync);
  ASSERT_EQ(Thread::State::INITIAL, thread.state);

  instruction->execute(thread);

  ASSERT_EQ(1, thread.pc);
  ASSERT_EQ(1, thread.sync);
  ASSERT_EQ(Thread::State::WAITING, thread.state);

  /* attributes */
  ASSERT_EQ(0, instruction->attributes());
}

/* EXIT ***********************************************************************/
TEST_F(InstructionSetTest, EXIT)
{
  instruction = Instruction::Set::create("EXIT", 1);

  ASSERT_EQ("EXIT", instruction->symbol());

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(0, thread.accu);
  ASSERT_EQ(Thread::State::INITIAL, thread.state);

  instruction->execute(thread);

  ASSERT_EQ(0, thread.pc);
  ASSERT_EQ(1, thread.accu);
  ASSERT_EQ(Thread::State::EXITING, thread.state);

  /* attributes */
  ASSERT_EQ(0, instruction->attributes());
}
