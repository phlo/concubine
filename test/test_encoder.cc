#include <gtest/gtest.h>

#include <fstream>

#include "encoder.hh"
#include "program.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct EncoderTest : public ::testing::Test
{
  Program         program;
  smtlib::Encoder encoder;

  EncoderTest () : program(), encoder(program, 0) {};
};

/* collectPredecessors ********************************************************/
TEST_F(EncoderTest, collectPredecessors)
{
  /* simple - no jumps etc. */
  program.add(Instruction::Set::create("LOAD",  1));
  program.add(Instruction::Set::create("ADDI",  1));
  program.add(Instruction::Set::create("STORE", 1));

  encoder.collectPredecessors();

  ASSERT_EQ(2, encoder.predecessors.size());

  ASSERT_TRUE(encoder.predecessors[1] == unordered_set<word>({0}));
  ASSERT_TRUE(encoder.predecessors[2] == unordered_set<word>({1}));

  /* jump to start */
  program.add(Instruction::Set::create("JMP", 0));

  encoder.collectPredecessors();

  ASSERT_EQ(4, encoder.predecessors.size());

  ASSERT_TRUE(encoder.predecessors[0] == unordered_set<word>({3}));
  ASSERT_TRUE(encoder.predecessors[1] == unordered_set<word>({0}));
  ASSERT_TRUE(encoder.predecessors[2] == unordered_set<word>({1}));
  ASSERT_TRUE(encoder.predecessors[3] == unordered_set<word>({2}));

  program.clear();
  encoder.predecessors.clear();

  /* two predecessors */
  program.add(Instruction::Set::create("LOAD",  1));
  program.add(Instruction::Set::create("ADDI",  1));
  program.add(Instruction::Set::create("JNZ",   1));

  encoder.collectPredecessors();

  ASSERT_EQ(2, encoder.predecessors.size());

  ASSERT_TRUE(encoder.predecessors[1] == unordered_set<word>({0, 2}));
  ASSERT_TRUE(encoder.predecessors[2] == unordered_set<word>({1}));
}

/* addHeader ******************************************************************/
TEST_F(EncoderTest, addHeader)
{
  program.path  = "program.asm";
  encoder.bound = 1;

  encoder.addHeader();

  string expected =
    "; program: " + program.path + "\n" +
    "; bound: " + to_string(encoder.bound) + "\n" +
    "\n" +
    "(set-logic QF_AUFBV)\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addStmtDeclarations ********************************************************/
TEST_F(EncoderTest, addStmtDeclarations)
{
  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("ADDI", 1));

  encoder.bound = 2;

  encoder.addStmtDeclarations();

  string expected = string() +
    "; activation - STMT_<bound>_<pc>\n" +
    "(declare-fun STMT_1_0 () Bool)\n" +
    "(declare-fun STMT_1_1 () Bool)\n" +
    "(declare-fun STMT_2_0 () Bool)\n" +
    "(declare-fun STMT_2_1 () Bool)\n" +
    "(declare-fun STMT_FINAL () Bool)\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addMemDeclarations *********************************************************/
TEST_F(EncoderTest, addMemDeclarations)
{
  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("ADDI", 1));

  encoder.bound = 2;

  encoder.addMemDeclarations();

  string expected = string() +
    "; mem - MEM_<bound>\n" +
    "(declare-fun MEM_0 () (_ BitVec 16))\n" +
    "(declare-fun MEM_1 () (_ BitVec 16))\n" +
    "(declare-fun MEM_2 () (_ BitVec 16))\n" +
    "(declare-fun MEM_FINAL () (_ BitVec 16))\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addAccuDeclarations ********************************************************/
TEST_F(EncoderTest, addAccuDeclarations)
{
  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("ADDI", 1));

  encoder.bound = 2;

  encoder.addAccuDeclarations();

  string expected = string() +
    "; accumulator - ACCU_<bound>\n" +
    "(declare-fun ACCU_0 () (_ BitVec 16))\n" +
    "(assert (= ACCU_0 #x0000))\n" +
    "(declare-fun ACCU_1 () (_ BitVec 16))\n" +
    "(declare-fun ACCU_2 () (_ BitVec 16))\n" +
    "(declare-fun ACCU_FINAL () (_ BitVec 16))\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addHeapDeclarations ********************************************************/
TEST_F(EncoderTest, addHeapDeclarations)
{
  program.add(Instruction::Set::create("ADDI", 1));
  program.add(Instruction::Set::create("ADDI", 1));

  encoder.bound = 2;

  encoder.addHeapDeclarations();

  string expected = string() +
    "; machine memory - HEAP_<bound>\n" +
    "(declare-fun HEAP_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n" +
    "(declare-fun HEAP_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n" +
    "(declare-fun HEAP_2 () (Array (_ BitVec 16) (_ BitVec 16)))\n" +
    "(declare-fun HEAP_FINAL () (Array (_ BitVec 16) (_ BitVec 16)))\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addExitDeclarations ********************************************************/
TEST_F(EncoderTest, addExitDeclarations)
{
  encoder.addExitDeclarations();

  string expected = string() +
    "; exit status\n" +
    "(declare-fun EXIT () Bool)\n" +
    "(declare-fun EXIT_CODE () (_ BitVec 16))\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* LoadStoreArithmetic ********************************************************/
TEST_F(EncoderTest, LoadStoreArithmetic)
{
  /* read expected smt formula from file */
  ifstream scheduleFile("data/load.store.arithmetic.encoded.smt");
  string schedule(( istreambuf_iterator<char>(scheduleFile) ),
                    istreambuf_iterator<char>());

  program = Program("data/load.store.arithmetic.asm");

  encoder.bound = 5;

  encoder.encode();

  ASSERT_STREQ(schedule.c_str(), encoder.formula.str().c_str());
}

// TODO: more tests for multi-threaded encoder
