#include <gtest/gtest.h>

#include <fstream>

#include "shell.hh"
#include "encoder.hh"
#include "program.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct EncoderTest : public ::testing::Test
{
  ProgramList     programs;
  SMTLibEncoder   encoder;

  EncoderTest () : programs(), encoder(programs, 0) {};
};

/* collectPredecessors ********************************************************/
TEST_F(EncoderTest, collectPredecessors)
{
  /* initialize with a single program */
  programs.push_back(make_shared<Program>());

  /* simple - no jumps etc. */
  programs[0]->add(Instruction::Set::create("LOAD",  1));
  programs[0]->add(Instruction::Set::create("ADDI",  1));
  programs[0]->add(Instruction::Set::create("STORE", 1));

  encoder.collectPredecessors();

  ASSERT_EQ(2, encoder.predecessors.size());

  ASSERT_TRUE(encoder.predecessors[1] == unordered_set<word>({0}));
  ASSERT_TRUE(encoder.predecessors[2] == unordered_set<word>({1}));

  /* jump to start */
  programs[0]->add(Instruction::Set::create("JMP", 0));

  encoder.collectPredecessors();

  ASSERT_EQ(4, encoder.predecessors.size());

  ASSERT_TRUE(encoder.predecessors[0] == unordered_set<word>({3}));
  ASSERT_TRUE(encoder.predecessors[1] == unordered_set<word>({0}));
  ASSERT_TRUE(encoder.predecessors[2] == unordered_set<word>({1}));
  ASSERT_TRUE(encoder.predecessors[3] == unordered_set<word>({2}));

  programs[0]->clear();
  encoder.predecessors.clear();

  /* two predecessors */
  programs[0]->add(Instruction::Set::create("LOAD",  1));
  programs[0]->add(Instruction::Set::create("ADDI",  1));
  programs[0]->add(Instruction::Set::create("JNZ",   1));

  encoder.collectPredecessors();

  ASSERT_EQ(2, encoder.predecessors.size());

  ASSERT_TRUE(encoder.predecessors[1] == unordered_set<word>({0, 2}));
  ASSERT_TRUE(encoder.predecessors[2] == unordered_set<word>({1}));
}

/* addHeader ******************************************************************/
TEST_F(EncoderTest, addHeader)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());
  programs.push_back(make_shared<Program>());
  programs.push_back(make_shared<Program>());
  
  programs[0]->path = "program1.asm";
  programs[1]->path = "program2.asm";
  programs[2]->path = "program3.asm";

  encoder.bound = 1;

  encoder.addHeader();

  string expected =
    "; bound: " + to_string(encoder.bound) + "\n" +
    "; programs: \n"
    ";   0: " + programs[0]->path + "\n" +
    ";   1: " + programs[1]->path + "\n" +
    ";   2: " + programs[2]->path + "\n" +
    "\n" +
    "(set-logic QF_AUFBV)\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addThreadDeclarations ******************************************************/
TEST_F(EncoderTest, addThreadDeclarations)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());
  programs.push_back(make_shared<Program>());
  programs.push_back(make_shared<Program>());

  encoder.bound = 2;

  encoder.addThreadDeclarations();

  string expected = string() +
    "; thread activation - THREAD_<step>_<thread>\n" +
    "(declare-fun THREAD_1_0 () Bool)\n" +
    "(declare-fun THREAD_1_1 () Bool)\n" +
    "(declare-fun THREAD_1_2 () Bool)\n" +
    "(declare-fun THREAD_2_0 () Bool)\n" +
    "(declare-fun THREAD_2_1 () Bool)\n" +
    "(declare-fun THREAD_2_2 () Bool)\n" +
    "\n" +
    "(declare-fun THREAD_FINAL () Bool)\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addStmtDeclarations ********************************************************/
TEST_F(EncoderTest, addStmtDeclarations)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());
  programs.push_back(programs[0]);
  programs.push_back(programs[0]);

  programs[0]->add(Instruction::Set::create("ADDI", 1));
  programs[0]->add(Instruction::Set::create("ADDI", 1));

  encoder.bound = 2;

  encoder.addStmtDeclarations();

  string expected = string() +
    "; program statement activation - STMT_<step>_<thread>_<pc>\n" +
    "(declare-fun STMT_1_0_0 () Bool)\n" +
    "(declare-fun STMT_1_0_1 () Bool)\n" +
    "(declare-fun STMT_1_1_0 () Bool)\n" +
    "(declare-fun STMT_1_1_1 () Bool)\n" +
    "(declare-fun STMT_1_2_0 () Bool)\n" +
    "(declare-fun STMT_1_2_1 () Bool)\n" +
    "(declare-fun STMT_2_0_0 () Bool)\n" +
    "(declare-fun STMT_2_0_1 () Bool)\n" +
    "(declare-fun STMT_2_1_0 () Bool)\n" +
    "(declare-fun STMT_2_1_1 () Bool)\n" +
    "(declare-fun STMT_2_2_0 () Bool)\n" +
    "(declare-fun STMT_2_2_1 () Bool)\n" +
    "\n" +
    "(declare-fun STMT_0_FINAL () Bool)\n" +
    "(declare-fun STMT_1_FINAL () Bool)\n" +
    "(declare-fun STMT_2_FINAL () Bool)\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addMemDeclarations *********************************************************/
TEST_F(EncoderTest, addMemDeclarations)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());
  programs.push_back(programs[0]);
  programs.push_back(programs[0]);

  encoder.bound = 2;

  encoder.addMemDeclarations();

  string expected = string() +
    "; cas memory register - MEM_<step>_<thread>\n" +
    "(declare-fun MEM_0 () (_ BitVec 16))\n" +
    "(declare-fun MEM_1_0 () (_ BitVec 16))\n" +
    "(declare-fun MEM_1_1 () (_ BitVec 16))\n" +
    "(declare-fun MEM_1_2 () (_ BitVec 16))\n" +
    "(declare-fun MEM_2_0 () (_ BitVec 16))\n" +
    "(declare-fun MEM_2_1 () (_ BitVec 16))\n" +
    "(declare-fun MEM_2_2 () (_ BitVec 16))\n" +
    "\n" +
    "(declare-fun MEM_0_FINAL () (_ BitVec 16))\n" +
    "(declare-fun MEM_1_FINAL () (_ BitVec 16))\n" +
    "(declare-fun MEM_2_FINAL () (_ BitVec 16))\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addAccuDeclarations ********************************************************/
TEST_F(EncoderTest, addAccuDeclarations)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());
  programs.push_back(programs[0]);
  programs.push_back(programs[0]);

  programs[0]->add(Instruction::Set::create("ADDI", 1));
  programs[0]->add(Instruction::Set::create("ADDI", 1));

  encoder.bound = 2;

  encoder.addAccuDeclarations();

  string expected = string() +
    "; accumulator - ACCU_<step>_<thread>\n" +
    "(declare-fun ACCU_0 () (_ BitVec 16))\n" +
    "(assert (= ACCU_0 #x0000))\n" +
    "(declare-fun ACCU_1_0 () (_ BitVec 16))\n" +
    "(declare-fun ACCU_1_1 () (_ BitVec 16))\n" +
    "(declare-fun ACCU_1_2 () (_ BitVec 16))\n" +
    "(declare-fun ACCU_2_0 () (_ BitVec 16))\n" +
    "(declare-fun ACCU_2_1 () (_ BitVec 16))\n" +
    "(declare-fun ACCU_2_2 () (_ BitVec 16))\n" +
    "\n" +
    "(declare-fun ACCU_0_FINAL () (_ BitVec 16))\n" +
    "(declare-fun ACCU_1_FINAL () (_ BitVec 16))\n" +
    "(declare-fun ACCU_2_FINAL () (_ BitVec 16))\n\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}

/* addHeapDeclarations ********************************************************/
TEST_F(EncoderTest, addHeapDeclarations)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());
  programs.push_back(programs[0]);
  programs.push_back(programs[0]);

  programs[0]->add(Instruction::Set::create("ADDI", 1));
  programs[0]->add(Instruction::Set::create("ADDI", 1));

  encoder.bound = 2;

  encoder.addHeapDeclarations();

  string expected = string() +
    "; machine memory - HEAP_<step>\n" +
    "(declare-fun HEAP_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n" +
    "(declare-fun HEAP_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n" +
    "(declare-fun HEAP_2 () (Array (_ BitVec 16) (_ BitVec 16)))\n" +
    "\n" +
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

/* addSingleThreadConstraints *************************************************/
TEST_F(EncoderTest, addSingleThreadConstraints)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());

  encoder.bound = 3;

  encoder.addThreadConstraints();

  string expected = string() +
    "; thread constraints (exactly one active at any step)\n" +
    "(assert THREAD_1_0)\n" +
    "(assert THREAD_2_0)\n" +
    "(assert THREAD_3_0)\n" +
    "\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());
}


/* addMultiThreadConstraints **************************************************/
TEST_F(EncoderTest, addMultiThreadConstraints)
{
  /* initialize with a couple of programs */
  programs.push_back(make_shared<Program>());
  programs.push_back(programs[0]);
  programs.push_back(programs[0]);

  encoder.bound = 3;

  encoder.addThreadConstraints();

  string expected = string() +
    "; thread constraints (exactly one active at any step)\n" +
    "(assert (or (not THREAD_1_0) (not THREAD_1_1)))\n" +
    "(assert (or (not THREAD_1_0) (not THREAD_1_2)))\n" +
    "(assert (or (not THREAD_1_1) (not THREAD_1_2)))\n" +
    "\n" +
    "(assert (or (not THREAD_2_0) (not THREAD_2_1)))\n" +
    "(assert (or (not THREAD_2_0) (not THREAD_2_2)))\n" +
    "(assert (or (not THREAD_2_1) (not THREAD_2_2)))\n" +
    "\n" +
    "(assert (or (not THREAD_3_0) (not THREAD_3_1)))\n" +
    "(assert (or (not THREAD_3_0) (not THREAD_3_2)))\n" +
    "(assert (or (not THREAD_3_1) (not THREAD_3_2)))\n" +
    "\n";

  ASSERT_STREQ(expected.c_str(), encoder.formula.str().c_str());

  Shell shell;

  encoder.formula.str("");
  encoder.formula.clear();

  encoder.addThreadDeclarations();
  encoder.addThreadConstraints();

  string formula = encoder.formula.str();

  string model = shell.run("boolector -m", formula);

  expected = string() +
    "sat\n" +
    "2 0 THREAD_1_0\n" +
    "3 1 THREAD_1_1\n" +
    "4 0 THREAD_1_2\n" +
    "5 1 THREAD_2_0\n" +
    "6 0 THREAD_2_1\n" +
    "7 0 THREAD_2_2\n" +
    "8 1 THREAD_3_0\n" +
    "9 0 THREAD_3_1\n" +
    "10 0 THREAD_3_2\n" +
    "11 0 THREAD_FINAL\n";

  ASSERT_STREQ(expected.c_str(), model.c_str());
}

///* LoadStoreArithmetic ********************************************************/
//TEST_F(EncoderTest, LoadStoreArithmetic)
//{
//  /* read expected smt formula from file */
//  ifstream scheduleFile("data/load.store.arithmetic.encoded.smt");
//  string schedule(( istreambuf_iterator<char>(scheduleFile) ),
//                    istreambuf_iterator<char>());
//
//  program = Program("data/load.store.arithmetic.asm");
//
//  encoder.bound = 5;
//
//  encoder.encode();
//
//  ASSERT_STREQ(schedule.c_str(), encoder.formula.str().c_str());
//}

// TODO: more tests for multi-threaded encoder
