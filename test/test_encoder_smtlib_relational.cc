#include <gtest/gtest.h>

#include <fstream>

#include "encoder.hh"
#include "smtlib.hh"

using namespace std;

struct SMTLibEncoderRelationalTest : public ::testing::Test
{
  string                      expected;
  ProgramList                 programs;
  SMTLibEncoderRelationalPtr  encoder = create_encoder(2, 1);

  SMTLibEncoderRelationalPtr create_encoder (const word bound, const word step)
    {
      SMTLibEncoderRelationalPtr e =
        make_shared<SMTLibEncoderRelational>(
          make_shared<ProgramList>(programs),
          bound,
          false);

      e->step = step;
      e->thread = 1;
      e->pc = 0;

      return e;
    }

  void reset_encoder (const word bound, unsigned long step)
    {
      encoder = create_encoder(bound, step);
    }

  void add_dummy_programs (unsigned num_threads)
    {
      for (size_t i = 0; i < num_threads; i++)
        {
          programs.push_back(ProgramPtr(new Program()));

          programs[i]->add(Instruction::Set::create("LOAD", 1));
          programs[i]->add(Instruction::Set::create("ADDI", 1));
          programs[i]->add(Instruction::Set::create("STORE", 1));
        }

      reset_encoder(2, 1);
    }

  void add_instruction_set (unsigned num_threads)
    {
      for (size_t i = 0; i < num_threads; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));

          programs[i]->add(Instruction::Set::create("LOAD", 1));  // 0
          programs[i]->add(Instruction::Set::create("STORE", 1)); // 1
          programs[i]->add(Instruction::Set::create("ADD", 1));   // 2
          programs[i]->add(Instruction::Set::create("ADDI", 1));  // 3
          programs[i]->add(Instruction::Set::create("SUB", 1));   // 4
          programs[i]->add(Instruction::Set::create("SUBI", 1));  // 5
          programs[i]->add(Instruction::Set::create("CMP", 1));   // 6
          programs[i]->add(Instruction::Set::create("JMP", 1));   // 7
          programs[i]->add(Instruction::Set::create("JZ", 1));    // 8
          programs[i]->add(Instruction::Set::create("JNZ", 1));   // 9
          programs[i]->add(Instruction::Set::create("JS", 1));    // 10
          programs[i]->add(Instruction::Set::create("JNS", 1));   // 11
          programs[i]->add(Instruction::Set::create("JNZNS", 1)); // 12
          programs[i]->add(Instruction::Set::create("MEM", 1));   // 13
          programs[i]->add(Instruction::Set::create("CAS", 1));   // 14
          programs[i]->add(Instruction::Set::create("SYNC", 1));  // 15
          programs[i]->add(Instruction::Set::create("EXIT", 1));  // 16
        }

      reset_encoder(2, 1);
    }
};

// std::string imply (std::string, std::string);
TEST_F(SMTLibEncoderRelationalTest, imply)
{
  ASSERT_EQ("(assert (=> foo bar))\n", encoder->imply("foo", "bar"));
}

// std::string assign_heap (std::string);
TEST_F(SMTLibEncoderRelationalTest, assign_heap)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= heap_1 (store heap_0 #x0000 #x0001))))\n",
    encoder->assign_heap(
      smtlib::store(
        encoder->heap_var(encoder->step - 1),
        smtlib::word2hex(0),
        smtlib::word2hex(1))));
}

// std::string assign_accu (std::string);
TEST_F(SMTLibEncoderRelationalTest, assign_accu)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 #x0000)))\n",
    encoder->assign_accu(smtlib::word2hex(0)));
}

// std::string assign_mem (std::string);
TEST_F(SMTLibEncoderRelationalTest, assign_mem)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= mem_1_1 #x0000)))\n",
    encoder->assign_mem(smtlib::word2hex(0)));
}

// std::string preserve_heap (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_heap)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n",
    encoder->preserve_heap());
}

// std::string preserve_accu (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_accu)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n",
    encoder->preserve_accu());
}

// std::string preserve_mem (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_mem)
{
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n",
    encoder->preserve_mem());
}

// std::string stmt_activation (word);
TEST_F(SMTLibEncoderRelationalTest, stmt_activation)
{
  add_dummy_programs(1);

  ASSERT_EQ(
    "(and (not stmt_2_1_0) stmt_2_1_1 (not stmt_2_1_2))",
    encoder->stmt_activation(1));

  /* last or unknown pc */
  ASSERT_EQ(
    "(and (not stmt_2_1_0) (not stmt_2_1_1) (not stmt_2_1_2))",
    encoder->stmt_activation(3));
}

// std::string activate_pc (word);
TEST_F(SMTLibEncoderRelationalTest, activate_pc)
{
  add_dummy_programs(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))))\n",
    encoder->activate_pc(1));

  /* last or unknown pc */
  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "(not stmt_2_1_2))))\n",
    encoder->activate_pc(3));

  /* step == bound */
  encoder->step = encoder->bound;

  ASSERT_EQ("", encoder->activate_pc(1));
}

// std::string activate_next (void);
TEST_F(SMTLibEncoderRelationalTest, activate_next)
{
  add_dummy_programs(1);

  encoder->pc = 1;

  ASSERT_EQ(
    "(assert (=> exec_1_1_1 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "stmt_2_1_2)))\n",
    encoder->activate_next());

  /* last pc */
  encoder->pc = 2;

  ASSERT_EQ(
    "(assert (=> exec_1_1_2 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "(not stmt_2_1_2))))\n",
    encoder->activate_next());

  /* step == bound */
  encoder->step = encoder->bound;

  ASSERT_EQ("", encoder->activate_next());
}

// std::string activate_jmp (std::string, word);
TEST_F(SMTLibEncoderRelationalTest, activate_jmp)
{
  add_dummy_programs(1);

  encoder->pc = 1;

  ASSERT_EQ(
    "(assert (=> exec_1_1_1 "
      "(ite foo "
        "(and "
          "stmt_2_1_0 "
          "(not stmt_2_1_1) "
          "(not stmt_2_1_2)) "
        "(and "
          "(not stmt_2_1_0) "
          "(not stmt_2_1_1) "
          "stmt_2_1_2))))\n",
    encoder->activate_jmp("foo", 0));

  /* last or unknown pc */
  encoder->pc = 2;

  ASSERT_EQ(
    "(assert (=> exec_1_1_2 "
      "(ite foo "
        "(and "
          "stmt_2_1_0 "
          "(not stmt_2_1_1) "
          "(not stmt_2_1_2)) "
        "(and "
          "(not stmt_2_1_0) "
          "(not stmt_2_1_1) "
          "(not stmt_2_1_2)))))\n",
    encoder->activate_jmp("foo", 0));

  /* step == bound */
  encoder->step = encoder->bound;

  ASSERT_EQ("", encoder->activate_jmp("foo", 0));
}

// void add_exit_code (void);
TEST_F(SMTLibEncoderRelationalTest, add_exit_code)
{
  encoder->add_exit_code();

  expected =
    "; exit code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit_code () (_ BitVec 16))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// void add_statement_declaration (void);
TEST_F(SMTLibEncoderRelationalTest, add_statement_declaration)
{
  add_dummy_programs(3);

  /* step 0 */
  encoder->step = 0;

  encoder->add_statement_declaration();

  expected =
    "; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_1_1_0 () Bool)\n"
    "(declare-fun stmt_1_1_1 () Bool)\n"
    "(declare-fun stmt_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_2_0 () Bool)\n"
    "(declare-fun stmt_1_2_1 () Bool)\n"
    "(declare-fun stmt_1_2_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_3_0 () Bool)\n"
    "(declare-fun stmt_1_3_1 () Bool)\n"
    "(declare-fun stmt_1_3_2 () Bool)\n"
    "\n"
    "; initial statement activation\n"
    "(assert stmt_1_1_0)\n"
    "(assert (not stmt_1_1_1))\n"
    "(assert (not stmt_1_1_2))\n"
    "\n"
    "(assert stmt_1_2_0)\n"
    "(assert (not stmt_1_2_1))\n"
    "(assert (not stmt_1_2_2))\n"
    "\n"
    "(assert stmt_1_3_0)\n"
    "(assert (not stmt_1_3_1))\n"
    "(assert (not stmt_1_3_2))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* step 1 */
  reset_encoder(2, 1);

  encoder->add_statement_declaration();

  expected =
    "; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "(declare-fun stmt_2_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "(declare-fun stmt_2_2_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_3_0 () Bool)\n"
    "(declare-fun stmt_2_3_1 () Bool)\n"
    "(declare-fun stmt_2_3_2 () Bool)\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* step 2 == bound */
  reset_encoder(2, 2);

  encoder->add_statement_declaration();

  ASSERT_EQ("", encoder->formula.str());

  /* verbosity */
  reset_encoder(2, 0);

  verbose = false;
  encoder->add_statement_declaration();
  verbose = true;

  expected =
    "(declare-fun stmt_1_1_0 () Bool)\n"
    "(declare-fun stmt_1_1_1 () Bool)\n"
    "(declare-fun stmt_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_2_0 () Bool)\n"
    "(declare-fun stmt_1_2_1 () Bool)\n"
    "(declare-fun stmt_1_2_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_3_0 () Bool)\n"
    "(declare-fun stmt_1_3_1 () Bool)\n"
    "(declare-fun stmt_1_3_2 () Bool)\n"
    "\n"
    "(assert stmt_1_1_0)\n"
    "(assert (not stmt_1_1_1))\n"
    "(assert (not stmt_1_1_2))\n"
    "\n"
    "(assert stmt_1_2_0)\n"
    "(assert (not stmt_1_2_1))\n"
    "(assert (not stmt_1_2_2))\n"
    "\n"
    "(assert stmt_1_3_0)\n"
    "(assert (not stmt_1_3_1))\n"
    "(assert (not stmt_1_3_2))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// void add_state_update (void);
TEST_F(SMTLibEncoderRelationalTest, add_state_update)
{
  add_dummy_programs(3);

  encoder->add_state_update();

  expected =
    "; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "(declare-fun accu_1_3 () (_ BitVec 16))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "(declare-fun mem_1_3 () (_ BitVec 16))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "; thread 1@0: LOAD\t1\n"
    "(assert (=> exec_1_1_0 (= accu_1_1 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))))\n"
    "\n"
    "; thread 1@1: ADDI\t1\n"
    "(assert (=> exec_1_1_1 (= accu_1_1 (bvadd accu_0_1 #x0001))))\n"
    "(assert (=> exec_1_1_1 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_1 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "stmt_2_1_2)))\n"
    "\n"
    "; thread 1@2: STORE\t1\n"
    "(assert (=> exec_1_1_2 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_2 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_2 (= heap_1 (store heap_0 #x0001 accu_0_1))))\n"
    "(assert (=> exec_1_1_2 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "(not stmt_2_1_2))))\n"
    "\n"
    "; thread 2@0: LOAD\t1\n"
    "(assert (=> exec_1_2_0 (= accu_1_2 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_2_0 (= mem_1_2 mem_0_2)))\n"
    "(assert (=> exec_1_2_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_2_0 "
      "(and "
        "(not stmt_2_2_0) "
        "stmt_2_2_1 "
        "(not stmt_2_2_2))))\n"
    "\n"
    "; thread 2@1: ADDI\t1\n"
    "(assert (=> exec_1_2_1 (= accu_1_2 (bvadd accu_0_2 #x0001))))\n"
    "(assert (=> exec_1_2_1 (= mem_1_2 mem_0_2)))\n"
    "(assert (=> exec_1_2_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_2_1 "
      "(and "
        "(not stmt_2_2_0) "
        "(not stmt_2_2_1) "
        "stmt_2_2_2)))\n"
    "\n"
    "; thread 2@2: STORE\t1\n"
    "(assert (=> exec_1_2_2 (= accu_1_2 accu_0_2)))\n"
    "(assert (=> exec_1_2_2 (= mem_1_2 mem_0_2)))\n"
    "(assert (=> exec_1_2_2 (= heap_1 (store heap_0 #x0001 accu_0_2))))\n"
    "(assert (=> exec_1_2_2 "
      "(and "
        "(not stmt_2_2_0) "
        "(not stmt_2_2_1) "
        "(not stmt_2_2_2))))\n"
    "\n"
    "; thread 3@0: LOAD\t1\n"
    "(assert (=> exec_1_3_0 (= accu_1_3 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_3_0 (= mem_1_3 mem_0_3)))\n"
    "(assert (=> exec_1_3_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_3_0 "
      "(and "
        "(not stmt_2_3_0) "
        "stmt_2_3_1 "
        "(not stmt_2_3_2))))\n"
    "\n"
    "; thread 3@1: ADDI\t1\n"
    "(assert (=> exec_1_3_1 (= accu_1_3 (bvadd accu_0_3 #x0001))))\n"
    "(assert (=> exec_1_3_1 (= mem_1_3 mem_0_3)))\n"
    "(assert (=> exec_1_3_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_3_1 "
      "(and "
        "(not stmt_2_3_0) "
        "(not stmt_2_3_1) "
        "stmt_2_3_2)))\n"
    "\n"
    "; thread 3@2: STORE\t1\n"
    "(assert (=> exec_1_3_2 (= accu_1_3 accu_0_3)))\n"
    "(assert (=> exec_1_3_2 (= mem_1_3 mem_0_3)))\n"
    "(assert (=> exec_1_3_2 (= heap_1 (store heap_0 #x0001 accu_0_3))))\n"
    "(assert (=> exec_1_3_2 "
      "(and "
        "(not stmt_2_3_0) "
        "(not stmt_2_3_1) "
        "(not stmt_2_3_2))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* step == bound */
  reset_encoder(2, 2);

  encoder->add_state_update();

  expected =
    "; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_2_1 () (_ BitVec 16))\n"
    "(declare-fun accu_2_2 () (_ BitVec 16))\n"
    "(declare-fun accu_2_3 () (_ BitVec 16))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_2_1 () (_ BitVec 16))\n"
    "(declare-fun mem_2_2 () (_ BitVec 16))\n"
    "(declare-fun mem_2_3 () (_ BitVec 16))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "; thread 1@0: LOAD\t1\n"
    "(assert (=> exec_2_1_0 (= accu_2_1 (select heap_1 #x0001))))\n"
    "(assert (=> exec_2_1_0 (= mem_2_1 mem_1_1)))\n"
    "(assert (=> exec_2_1_0 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 1@1: ADDI\t1\n"
    "(assert (=> exec_2_1_1 (= accu_2_1 (bvadd accu_1_1 #x0001))))\n"
    "(assert (=> exec_2_1_1 (= mem_2_1 mem_1_1)))\n"
    "(assert (=> exec_2_1_1 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 1@2: STORE\t1\n"
    "(assert (=> exec_2_1_2 (= accu_2_1 accu_1_1)))\n"
    "(assert (=> exec_2_1_2 (= mem_2_1 mem_1_1)))\n"
    "(assert (=> exec_2_1_2 (= heap_2 (store heap_1 #x0001 accu_1_1))))\n"
    "\n"
    "; thread 2@0: LOAD\t1\n"
    "(assert (=> exec_2_2_0 (= accu_2_2 (select heap_1 #x0001))))\n"
    "(assert (=> exec_2_2_0 (= mem_2_2 mem_1_2)))\n"
    "(assert (=> exec_2_2_0 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 2@1: ADDI\t1\n"
    "(assert (=> exec_2_2_1 (= accu_2_2 (bvadd accu_1_2 #x0001))))\n"
    "(assert (=> exec_2_2_1 (= mem_2_2 mem_1_2)))\n"
    "(assert (=> exec_2_2_1 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 2@2: STORE\t1\n"
    "(assert (=> exec_2_2_2 (= accu_2_2 accu_1_2)))\n"
    "(assert (=> exec_2_2_2 (= mem_2_2 mem_1_2)))\n"
    "(assert (=> exec_2_2_2 (= heap_2 (store heap_1 #x0001 accu_1_2))))\n"
    "\n"
    "; thread 3@0: LOAD\t1\n"
    "(assert (=> exec_2_3_0 (= accu_2_3 (select heap_1 #x0001))))\n"
    "(assert (=> exec_2_3_0 (= mem_2_3 mem_1_3)))\n"
    "(assert (=> exec_2_3_0 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 3@1: ADDI\t1\n"
    "(assert (=> exec_2_3_1 (= accu_2_3 (bvadd accu_1_3 #x0001))))\n"
    "(assert (=> exec_2_3_1 (= mem_2_3 mem_1_3)))\n"
    "(assert (=> exec_2_3_1 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 3@2: STORE\t1\n"
    "(assert (=> exec_2_3_2 (= accu_2_3 accu_1_3)))\n"
    "(assert (=> exec_2_3_2 (= mem_2_3 mem_1_3)))\n"
    "(assert (=> exec_2_3_2 (= heap_2 (store heap_1 #x0001 accu_1_3))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(2, 1);

  verbose = false;
  encoder->add_state_update();
  verbose = true;

  expected =
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "(declare-fun accu_1_3 () (_ BitVec 16))\n"
    "\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "(declare-fun mem_1_3 () (_ BitVec 16))\n"
    "\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (=> exec_1_1_0 (= accu_1_1 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))))\n"
    "\n"
    "(assert (=> exec_1_1_1 (= accu_1_1 (bvadd accu_0_1 #x0001))))\n"
    "(assert (=> exec_1_1_1 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_1 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "stmt_2_1_2)))\n"
    "\n"
    "(assert (=> exec_1_1_2 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_2 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_2 (= heap_1 (store heap_0 #x0001 accu_0_1))))\n"
    "(assert (=> exec_1_1_2 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "(not stmt_2_1_2))))\n"
    "\n"
    "(assert (=> exec_1_2_0 (= accu_1_2 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_2_0 (= mem_1_2 mem_0_2)))\n"
    "(assert (=> exec_1_2_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_2_0 "
      "(and "
        "(not stmt_2_2_0) "
        "stmt_2_2_1 "
        "(not stmt_2_2_2))))\n"
    "\n"
    "(assert (=> exec_1_2_1 (= accu_1_2 (bvadd accu_0_2 #x0001))))\n"
    "(assert (=> exec_1_2_1 (= mem_1_2 mem_0_2)))\n"
    "(assert (=> exec_1_2_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_2_1 "
      "(and "
        "(not stmt_2_2_0) "
        "(not stmt_2_2_1) "
        "stmt_2_2_2)))\n"
    "\n"
    "(assert (=> exec_1_2_2 (= accu_1_2 accu_0_2)))\n"
    "(assert (=> exec_1_2_2 (= mem_1_2 mem_0_2)))\n"
    "(assert (=> exec_1_2_2 (= heap_1 (store heap_0 #x0001 accu_0_2))))\n"
    "(assert (=> exec_1_2_2 "
      "(and "
        "(not stmt_2_2_0) "
        "(not stmt_2_2_1) "
        "(not stmt_2_2_2))))\n"
    "\n"
    "(assert (=> exec_1_3_0 (= accu_1_3 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_3_0 (= mem_1_3 mem_0_3)))\n"
    "(assert (=> exec_1_3_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_3_0 "
      "(and "
        "(not stmt_2_3_0) "
        "stmt_2_3_1 "
        "(not stmt_2_3_2))))\n"
    "\n"
    "(assert (=> exec_1_3_1 (= accu_1_3 (bvadd accu_0_3 #x0001))))\n"
    "(assert (=> exec_1_3_1 (= mem_1_3 mem_0_3)))\n"
    "(assert (=> exec_1_3_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_3_1 "
      "(and "
        "(not stmt_2_3_0) "
        "(not stmt_2_3_1) "
        "stmt_2_3_2)))\n"
    "\n"
    "(assert (=> exec_1_3_2 (= accu_1_3 accu_0_3)))\n"
    "(assert (=> exec_1_3_2 (= mem_1_3 mem_0_3)))\n"
    "(assert (=> exec_1_3_2 (= heap_1 (store heap_0 #x0001 accu_0_3))))\n"
    "(assert (=> exec_1_3_2 "
      "(and "
        "(not stmt_2_3_0) "
        "(not stmt_2_3_1) "
        "(not stmt_2_3_2))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// void add_state_preservation (void);
TEST_F(SMTLibEncoderRelationalTest, add_state_preservation)
{
  add_instruction_set(3);

  encoder->add_state_preservation();

  expected =
    "; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= accu_1_1 accu_0_1)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= mem_1_1 mem_0_1)))\n"
    "\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_0 stmt_1_1_0)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_1 stmt_1_1_1)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_2 stmt_1_1_2)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_3 stmt_1_1_3)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_4 stmt_1_1_4)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_5 stmt_1_1_5)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_6 stmt_1_1_6)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_7 stmt_1_1_7)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_8 stmt_1_1_8)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_9 stmt_1_1_9)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_10 stmt_1_1_10)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_11 stmt_1_1_11)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_12 stmt_1_1_12)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_13 stmt_1_1_13)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_14 stmt_1_1_14)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_15 stmt_1_1_15)))\n"
    "(assert (=> (not (or thread_1_1 sync_1_1)) (= stmt_2_1_16 stmt_1_1_16)))\n"
    "\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= accu_1_2 accu_0_2)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= mem_1_2 mem_0_2)))\n"
    "\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_0 stmt_1_2_0)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_1 stmt_1_2_1)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_2 stmt_1_2_2)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_3 stmt_1_2_3)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_4 stmt_1_2_4)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_5 stmt_1_2_5)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_6 stmt_1_2_6)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_7 stmt_1_2_7)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_8 stmt_1_2_8)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_9 stmt_1_2_9)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_10 stmt_1_2_10)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_11 stmt_1_2_11)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_12 stmt_1_2_12)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_13 stmt_1_2_13)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_14 stmt_1_2_14)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_15 stmt_1_2_15)))\n"
    "(assert (=> (not (or thread_1_2 sync_1_1)) (= stmt_2_2_16 stmt_1_2_16)))\n"
    "\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= accu_1_3 accu_0_3)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= mem_1_3 mem_0_3)))\n"
    "\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_0 stmt_1_3_0)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_1 stmt_1_3_1)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_2 stmt_1_3_2)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_3 stmt_1_3_3)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_4 stmt_1_3_4)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_5 stmt_1_3_5)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_6 stmt_1_3_6)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_7 stmt_1_3_7)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_8 stmt_1_3_8)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_9 stmt_1_3_9)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_10 stmt_1_3_10)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_11 stmt_1_3_11)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_12 stmt_1_3_12)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_13 stmt_1_3_13)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_14 stmt_1_3_14)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_15 stmt_1_3_15)))\n"
    "(assert (=> (not (or thread_1_3 sync_1_1)) (= stmt_2_3_16 stmt_1_3_16)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* step == bound */
  reset_encoder(2, 2);

  encoder->add_state_preservation();

  expected =
    "; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (not (or thread_2_1 sync_2_1)) (= accu_2_1 accu_1_1)))\n"
    "(assert (=> (not (or thread_2_1 sync_2_1)) (= mem_2_1 mem_1_1)))\n"
    "\n"
    "(assert (=> (not (or thread_2_2 sync_2_1)) (= accu_2_2 accu_1_2)))\n"
    "(assert (=> (not (or thread_2_2 sync_2_1)) (= mem_2_2 mem_1_2)))\n"
    "\n"
    "(assert (=> (not (or thread_2_3 sync_2_1)) (= accu_2_3 accu_1_3)))\n"
    "(assert (=> (not (or thread_2_3 sync_2_1)) (= mem_2_3 mem_1_3)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(2, 2);

  verbose = false;
  encoder->add_state_preservation();
  verbose = true;

  expected =
    "(assert (=> (not (or thread_2_1 sync_2_1)) (= accu_2_1 accu_1_1)))\n"
    "(assert (=> (not (or thread_2_1 sync_2_1)) (= mem_2_1 mem_1_1)))\n"
    "\n"
    "(assert (=> (not (or thread_2_2 sync_2_1)) (= accu_2_2 accu_1_2)))\n"
    "(assert (=> (not (or thread_2_2 sync_2_1)) (= mem_2_2 mem_1_2)))\n"
    "\n"
    "(assert (=> (not (or thread_2_3 sync_2_1)) (= accu_2_3 accu_1_3)))\n"
    "(assert (=> (not (or thread_2_3 sync_2_1)) (= mem_2_3 mem_1_3)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// virtual void encode (void);
// TODO
#include "boolector.hh"
TEST_F(SMTLibEncoderRelationalTest, encode)
{
  /* concurrent increment using SYNC */
  programs.push_back(
    shared_ptr<Program>(
      // new Program("data/increment.sync.thread.0.asm")));
      new Program("data/increment.cas.asm")));
  programs.push_back(
    shared_ptr<Program>(
      // new Program("data/increment.sync.thread.n.asm")));
      new Program("data/increment.cas.asm")));

  encoder =
    make_shared<SMTLibEncoderRelational>(
      make_shared<ProgramList>(programs), 12);

  ifstream ifs("data/increment.sync.functional.t2.k8.smt2");
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  EXPECT_EQ("", encoder->formula.str());

  Boolector btor;

  string formula = encoder->formula.str();

  ASSERT_TRUE(btor.sat(formula));
}

// virtual std::string encode (Load &);
TEST_F(SMTLibEncoderRelationalTest, LOAD)
{
  add_dummy_programs(1);

  Load load = Load(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(load));

  /* indirect */
  load.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (select heap_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(load));
}

// virtual std::string encode (Store &);
TEST_F(SMTLibEncoderRelationalTest, STORE)
{
  add_dummy_programs(1);

  Store store = Store(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 (store heap_0 #x0001 accu_0_1))))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(store));

  /* indirect */
  store.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 "
      "(= heap_1 (store heap_0 (select heap_0 #x0001) accu_0_1))))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(store));
}

// virtual std::string encode (Add &);
TEST_F(SMTLibEncoderRelationalTest, ADD)
{
  add_dummy_programs(1);

  Add add = Add(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvadd accu_0_1 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(add));

  /* indirect */
  add.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvadd accu_0_1 (select heap_0 (select heap_0 #x0001))))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(add));
}

// virtual std::string encode (Addi &);
TEST_F(SMTLibEncoderRelationalTest, ADDI)
{
  add_dummy_programs(1);

  Addi addi = Addi(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvadd accu_0_1 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(addi));
}

// virtual std::string encode (Sub &);
TEST_F(SMTLibEncoderRelationalTest, SUB)
{
  add_dummy_programs(1);

  Sub sub = Sub(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvsub accu_0_1 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(sub));

  /* indirect */
  sub.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvsub accu_0_1 (select heap_0 (select heap_0 #x0001))))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(sub));
}

// virtual std::string encode (Subi &);
TEST_F(SMTLibEncoderRelationalTest, SUBI)
{
  add_dummy_programs(1);

  Subi subi = Subi(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvsub accu_0_1 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(subi));
}

// virtual std::string encode (Cmp &);
TEST_F(SMTLibEncoderRelationalTest, CMP)
{
  add_dummy_programs(1);

  Cmp cmp = Cmp(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvsub accu_0_1 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(cmp));

  /* indirect */
  cmp.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (bvsub accu_0_1 (select heap_0 (select heap_0 #x0001))))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(cmp));
}

// virtual std::string encode (Jmp &);
TEST_F(SMTLibEncoderRelationalTest, JMP)
{
  add_dummy_programs(1);

  Jmp jmp = Jmp(2);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "(not stmt_2_1_1) "
        "stmt_2_1_2)"
    "))\n",
    encoder->encode(jmp));
}

// virtual std::string encode (Jz &);
TEST_F(SMTLibEncoderRelationalTest, JZ)
{
  add_dummy_programs(1);

  Jz jz = Jz(2);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(ite (= accu_1_1 #x0000) "
        "(and "
          "(not stmt_2_1_0) "
          "(not stmt_2_1_1) "
          "stmt_2_1_2) "
        "(and "
          "(not stmt_2_1_0) "
          "stmt_2_1_1 "
          "(not stmt_2_1_2))"
    ")))\n",
    encoder->encode(jz));
}

// virtual std::string encode (Jnz &);
TEST_F(SMTLibEncoderRelationalTest, JNZ)
{
  add_dummy_programs(1);

  Jnz jnz = Jnz(2);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(ite (not (= accu_1_1 #x0000)) "
        "(and "
          "(not stmt_2_1_0) "
          "(not stmt_2_1_1) "
          "stmt_2_1_2) "
        "(and "
          "(not stmt_2_1_0) "
          "stmt_2_1_1 "
          "(not stmt_2_1_2))"
    ")))\n",
    encoder->encode(jnz));
}

// virtual std::string encode (Js &);
TEST_F(SMTLibEncoderRelationalTest, JS)
{
  add_dummy_programs(1);

  Js js = Js(2);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(ite (= #b1 ((_ extract 15 15) accu_1_1)) "
        "(and "
          "(not stmt_2_1_0) "
          "(not stmt_2_1_1) "
          "stmt_2_1_2) "
        "(and "
          "(not stmt_2_1_0) "
          "stmt_2_1_1 "
          "(not stmt_2_1_2))"
    ")))\n",
    encoder->encode(js));
}

// virtual std::string encode (Jns &);
TEST_F(SMTLibEncoderRelationalTest, JNS)
{
  add_dummy_programs(1);

  Jns jns = Jns(2);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(ite (= #b0 ((_ extract 15 15) accu_1_1)) "
        "(and "
          "(not stmt_2_1_0) "
          "(not stmt_2_1_1) "
          "stmt_2_1_2) "
        "(and "
          "(not stmt_2_1_0) "
          "stmt_2_1_1 "
          "(not stmt_2_1_2))"
    ")))\n",
    encoder->encode(jns));
}

// virtual std::string encode (Jnzns &);
TEST_F(SMTLibEncoderRelationalTest, JNZNS)
{
  add_dummy_programs(1);

  Jnzns jnzns = Jnzns(2);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(ite "
        "(and (not (= accu_1_1 #x0000)) (= #b0 ((_ extract 15 15) accu_1_1))) "
        "(and "
          "(not stmt_2_1_0) "
          "(not stmt_2_1_1) "
          "stmt_2_1_2) "
        "(and "
          "(not stmt_2_1_0) "
          "stmt_2_1_1 "
          "(not stmt_2_1_2))"
    ")))\n",
    encoder->encode(jnzns));
}

// virtual std::string encode (Mem &);
TEST_F(SMTLibEncoderRelationalTest, MEM)
{
  add_dummy_programs(1);

  Mem mem = Mem(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 accu_1_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(mem));

  /* indirect */
  mem.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 "
      "(= accu_1_1 (select heap_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 accu_1_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(mem));
}

// virtual std::string encode (Cas &);
TEST_F(SMTLibEncoderRelationalTest, CAS)
{
  add_dummy_programs(1);

  Cas cas = Cas(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 "
      "(ite (= mem_0_1 (select heap_0 #x0001)) "
        "(store heap_0 #x0001 accu_0_1) "
        "heap_0))))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(cas));

  /* indirect */
  cas.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 "
      "(ite (= mem_0_1 (select heap_0 (select heap_0 #x0001))) "
        "(store heap_0 (select heap_0 #x0001) accu_0_1) "
        "heap_0))))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(cas));
}

// virtual std::string encode (Sync &);
TEST_F(SMTLibEncoderRelationalTest, SYNC)
{
  add_dummy_programs(1);

  Sync sync = Sync(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 "
      "(and "
        "(not stmt_2_1_0) "
        "stmt_2_1_1 "
        "(not stmt_2_1_2))"
    "))\n",
    encoder->encode(sync));
}

// virtual std::string encode (Exit &);
TEST_F(SMTLibEncoderRelationalTest, EXIT)
{
  add_dummy_programs(1);

  Exit exit = Exit(1);

  ASSERT_EQ(
    "(assert (=> exec_1_1_0 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> exec_1_1_0 (= mem_1_1 mem_0_1)))\n"
    "(assert (=> exec_1_1_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_1_0 (= exit_code #x0001)))\n",
    encoder->encode(exit));
}
