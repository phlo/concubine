#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "smtlib.hh"

using namespace std;

struct SMTLibEncoderRelationalTest : public ::testing::Test
{
  Program_list_ptr            programs {make_shared<Program_list>()};
  SMTLibEncoderRelational_ptr encoder {create_encoder(2, 1)};

  SMTLibEncoderRelational_ptr create_encoder (
                                              const word_t bound,
                                              const word_t step
                                             )
    {
      SMTLibEncoderRelational_ptr e =
        make_shared<SMTLibEncoderRelational>(programs, bound, false);

      e->step = step;
      e->thread = 0;
      e->pc = 0;

      return e;
    }

  void reset_encoder (const word_t bound, bound_t step)
    {
      encoder = create_encoder(bound, step);
    }

  void add_dummy_programs (unsigned num_threads)
    {
      for (size_t i = 0; i < num_threads; i++)
        {
          programs->push_back(make_shared<Program>());

          (*programs)[i]->push_back(Instruction::Set::create("LOAD", 1));
          (*programs)[i]->push_back(Instruction::Set::create("ADDI", 1));
          (*programs)[i]->push_back(Instruction::Set::create("STORE", 1));
        }

      reset_encoder(2, 1);
    }

  void add_instruction_set (unsigned num_threads)
    {
      for (size_t i = 0; i < num_threads; i++)
        {
          programs->push_back(shared_ptr<Program>(new Program()));

          (*programs)[i]->push_back(Instruction::Set::create("LOAD", 1));  // 0
          (*programs)[i]->push_back(Instruction::Set::create("STORE", 1)); // 1
          (*programs)[i]->push_back(Instruction::Set::create("ADD", 1));   // 2
          (*programs)[i]->push_back(Instruction::Set::create("ADDI", 1));  // 3
          (*programs)[i]->push_back(Instruction::Set::create("SUB", 1));   // 4
          (*programs)[i]->push_back(Instruction::Set::create("SUBI", 1));  // 5
          (*programs)[i]->push_back(Instruction::Set::create("CMP", 1));   // 6
          (*programs)[i]->push_back(Instruction::Set::create("JMP", 1));   // 7
          (*programs)[i]->push_back(Instruction::Set::create("JZ", 1));    // 8
          (*programs)[i]->push_back(Instruction::Set::create("JNZ", 1));   // 9
          (*programs)[i]->push_back(Instruction::Set::create("JS", 1));    // 10
          (*programs)[i]->push_back(Instruction::Set::create("JNS", 1));   // 11
          (*programs)[i]->push_back(Instruction::Set::create("JNZNS", 1)); // 12
          (*programs)[i]->push_back(Instruction::Set::create("MEM", 1));   // 13
          (*programs)[i]->push_back(Instruction::Set::create("CAS", 1));   // 14
          (*programs)[i]->push_back(Instruction::Set::create("CHECK", 1)); // 15
          (*programs)[i]->push_back(Instruction::Set::create("EXIT", 1));  // 16
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
    "(assert (=> exec_1_0_0 (= heap_1 (store heap_0 #x0000 #x0001))))\n",
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
    "(assert (=> exec_1_0_0 (= accu_1_0 #x0000)))\n",
    encoder->assign_accu(smtlib::word2hex(0)));
}

// std::string assign_mem (std::string);
TEST_F(SMTLibEncoderRelationalTest, assign_mem)
{
  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= mem_1_0 #x0000)))\n",
    encoder->assign_mem(smtlib::word2hex(0)));
}

// std::string preserve_heap (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_heap)
{
  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n",
    encoder->preserve_heap());
}

// std::string preserve_accu (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_accu)
{
  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n",
    encoder->preserve_accu());
}

// std::string preserve_mem (void);
TEST_F(SMTLibEncoderRelationalTest, preserve_mem)
{
  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n",
    encoder->preserve_mem());
}

// std::string stmt_activation (word_t);
TEST_F(SMTLibEncoderRelationalTest, stmt_activation)
{
  add_dummy_programs(1);

  ASSERT_EQ(
    "(and (not stmt_2_0_0) stmt_2_0_1 (not stmt_2_0_2))",
    encoder->stmt_activation(1));

  /* last or unknown pc */
  ASSERT_EQ(
    "(and (not stmt_2_0_0) (not stmt_2_0_1) (not stmt_2_0_2))",
    encoder->stmt_activation(3));
}

// std::string activate_pc (word_t);
TEST_F(SMTLibEncoderRelationalTest, activate_pc)
{
  add_dummy_programs(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))))\n",
    encoder->activate_pc(1));

  /* last or unknown pc */
  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "(not stmt_2_0_2))))\n",
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
    "(assert (=> exec_1_0_1 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "stmt_2_0_2)))\n",
    encoder->activate_next());

  /* last pc */
  encoder->pc = 2;

  ASSERT_EQ(
    "(assert (=> exec_1_0_2 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "(not stmt_2_0_2))))\n",
    encoder->activate_next());

  /* step == bound */
  encoder->step = encoder->bound;

  ASSERT_EQ("", encoder->activate_next());
}

// std::string activate_jmp (std::string, word_t);
TEST_F(SMTLibEncoderRelationalTest, activate_jmp)
{
  add_dummy_programs(1);

  encoder->pc = 1;

  ASSERT_EQ(
    "(assert (=> exec_1_0_1 "
      "(ite foo "
        "(and "
          "stmt_2_0_0 "
          "(not stmt_2_0_1) "
          "(not stmt_2_0_2)) "
        "(and "
          "(not stmt_2_0_0) "
          "(not stmt_2_0_1) "
          "stmt_2_0_2))))\n",
    encoder->activate_jmp("foo", 0));

  /* last or unknown pc */
  encoder->pc = 2;

  ASSERT_EQ(
    "(assert (=> exec_1_0_2 "
      "(ite foo "
        "(and "
          "stmt_2_0_0 "
          "(not stmt_2_0_1) "
          "(not stmt_2_0_2)) "
        "(and "
          "(not stmt_2_0_0) "
          "(not stmt_2_0_1) "
          "(not stmt_2_0_2)))))\n",
    encoder->activate_jmp("foo", 0));

  /* step == bound */
  encoder->step = encoder->bound;

  ASSERT_EQ("", encoder->activate_jmp("foo", 0));
}

// void add_exit_code (void);
TEST_F(SMTLibEncoderRelationalTest, add_exit_code)
{
  /* no call to EXIT */
  add_dummy_programs(3);

  encoder->add_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (= exit-code #x0000))\n",
    encoder->formula.str());

  reset_encoder(3, 1);

  /* step == bound */
  for (const auto & program : *programs)
    program->push_back(Instruction::Set::create("EXIT", 1));

  reset_encoder(3, 3);

  encoder->add_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (not exit_3) (= exit-code #x0000)))\n",
    encoder->formula.str());
}

// void add_statement_declaration (void);
TEST_F(SMTLibEncoderRelationalTest, add_statement_declaration)
{
  add_dummy_programs(3);

  /* step 0 */
  encoder->step = 0;

  encoder->add_statement_declaration();

  ASSERT_EQ(
    "; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_1_0_0 () Bool)\n"
    "(declare-fun stmt_1_0_1 () Bool)\n"
    "(declare-fun stmt_1_0_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_1_0 () Bool)\n"
    "(declare-fun stmt_1_1_1 () Bool)\n"
    "(declare-fun stmt_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_2_0 () Bool)\n"
    "(declare-fun stmt_1_2_1 () Bool)\n"
    "(declare-fun stmt_1_2_2 () Bool)\n"
    "\n"
    "; initial statement activation\n"
    "(assert stmt_1_0_0)\n"
    "(assert (not stmt_1_0_1))\n"
    "(assert (not stmt_1_0_2))\n"
    "\n"
    "(assert stmt_1_1_0)\n"
    "(assert (not stmt_1_1_1))\n"
    "(assert (not stmt_1_1_2))\n"
    "\n"
    "(assert stmt_1_2_0)\n"
    "(assert (not stmt_1_2_1))\n"
    "(assert (not stmt_1_2_2))\n\n",
    encoder->formula.str());

  /* step 1 */
  reset_encoder(2, 1);

  encoder->add_statement_declaration();

  ASSERT_EQ(
    "; statement activation forward declaration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_2_0_0 () Bool)\n"
    "(declare-fun stmt_2_0_1 () Bool)\n"
    "(declare-fun stmt_2_0_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "(declare-fun stmt_2_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "(declare-fun stmt_2_2_2 () Bool)\n\n",
    encoder->formula.str());

  /* step 2 == bound */
  reset_encoder(2, 2);

  encoder->add_statement_declaration();

  ASSERT_EQ("", encoder->formula.str());

  /* verbosity */
  reset_encoder(2, 0);

  verbose = false;
  encoder->add_statement_declaration();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun stmt_1_0_0 () Bool)\n"
    "(declare-fun stmt_1_0_1 () Bool)\n"
    "(declare-fun stmt_1_0_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_1_0 () Bool)\n"
    "(declare-fun stmt_1_1_1 () Bool)\n"
    "(declare-fun stmt_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_1_2_0 () Bool)\n"
    "(declare-fun stmt_1_2_1 () Bool)\n"
    "(declare-fun stmt_1_2_2 () Bool)\n"
    "\n"
    "(assert stmt_1_0_0)\n"
    "(assert (not stmt_1_0_1))\n"
    "(assert (not stmt_1_0_2))\n"
    "\n"
    "(assert stmt_1_1_0)\n"
    "(assert (not stmt_1_1_1))\n"
    "(assert (not stmt_1_1_2))\n"
    "\n"
    "(assert stmt_1_2_0)\n"
    "(assert (not stmt_1_2_1))\n"
    "(assert (not stmt_1_2_2))\n\n",
    encoder->formula.str());
}

// void add_state_update (void);
TEST_F(SMTLibEncoderRelationalTest, add_state_update)
{
  add_dummy_programs(3);

  encoder->add_state_update();

  ASSERT_EQ(
    "; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "; thread 0@0: LOAD\t1\n"
    "(assert (=> exec_1_0_0 (= accu_1_0 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))))\n"
    "\n"
    "; thread 0@1: ADDI\t1\n"
    "(assert (=> exec_1_0_1 (= accu_1_0 (bvadd accu_0_0 #x0001))))\n"
    "(assert (=> exec_1_0_1 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_1 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "stmt_2_0_2)))\n"
    "\n"
    "; thread 0@2: STORE\t1\n"
    "(assert (=> exec_1_0_2 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_2 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_2 (= heap_1 (store heap_0 #x0001 accu_0_0))))\n"
    "(assert (=> exec_1_0_2 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "(not stmt_2_0_2))))\n"
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
        "(not stmt_2_2_2))))\n\n",
    encoder->formula.str());

  /* step == bound */
  reset_encoder(2, 2);

  encoder->add_state_update();

  ASSERT_EQ(
    "; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_2_0 () (_ BitVec 16))\n"
    "(declare-fun accu_2_1 () (_ BitVec 16))\n"
    "(declare-fun accu_2_2 () (_ BitVec 16))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_2_0 () (_ BitVec 16))\n"
    "(declare-fun mem_2_1 () (_ BitVec 16))\n"
    "(declare-fun mem_2_2 () (_ BitVec 16))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "; thread 0@0: LOAD\t1\n"
    "(assert (=> exec_2_0_0 (= accu_2_0 (select heap_1 #x0001))))\n"
    "(assert (=> exec_2_0_0 (= mem_2_0 mem_1_0)))\n"
    "(assert (=> exec_2_0_0 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 0@1: ADDI\t1\n"
    "(assert (=> exec_2_0_1 (= accu_2_0 (bvadd accu_1_0 #x0001))))\n"
    "(assert (=> exec_2_0_1 (= mem_2_0 mem_1_0)))\n"
    "(assert (=> exec_2_0_1 (= heap_2 heap_1)))\n"
    "\n"
    "; thread 0@2: STORE\t1\n"
    "(assert (=> exec_2_0_2 (= accu_2_0 accu_1_0)))\n"
    "(assert (=> exec_2_0_2 (= mem_2_0 mem_1_0)))\n"
    "(assert (=> exec_2_0_2 (= heap_2 (store heap_1 #x0001 accu_1_0))))\n"
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
    "(assert (=> exec_2_2_2 (= heap_2 (store heap_1 #x0001 accu_1_2))))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(2, 1);

  verbose = false;
  encoder->add_state_update();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n"
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (=> exec_1_0_0 (= accu_1_0 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))))\n"
    "\n"
    "(assert (=> exec_1_0_1 (= accu_1_0 (bvadd accu_0_0 #x0001))))\n"
    "(assert (=> exec_1_0_1 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_1 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_1 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "stmt_2_0_2)))\n"
    "\n"
    "(assert (=> exec_1_0_2 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_2 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_2 (= heap_1 (store heap_0 #x0001 accu_0_0))))\n"
    "(assert (=> exec_1_0_2 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "(not stmt_2_0_2))))\n"
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
        "(not stmt_2_2_2))))\n\n",
    encoder->formula.str());
}

// void add_state_preservation (void);
TEST_F(SMTLibEncoderRelationalTest, add_state_preservation)
{
  add_instruction_set(3);

  encoder->add_state_preservation();

  ASSERT_EQ(
    "; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun preserve_1_0 () Bool)\n"
    "(assert (= preserve_1_0 (not thread_1_0)))\n"
    "\n"
    "(assert (=> preserve_1_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> preserve_1_0 (= mem_1_0 mem_0_0)))\n"
    "\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_0 stmt_1_0_0)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_1 stmt_1_0_1)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_2 stmt_1_0_2)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_3 stmt_1_0_3)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_4 stmt_1_0_4)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_5 stmt_1_0_5)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_6 stmt_1_0_6)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_7 stmt_1_0_7)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_8 stmt_1_0_8)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_9 stmt_1_0_9)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_10 stmt_1_0_10)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_11 stmt_1_0_11)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_12 stmt_1_0_12)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_13 stmt_1_0_13)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_14 stmt_1_0_14)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_15 stmt_1_0_15)))\n"
    "(assert (=> preserve_1_0 (= stmt_2_0_16 stmt_1_0_16)))\n"
    "\n"
    "(declare-fun preserve_1_1 () Bool)\n"
    "(assert (= preserve_1_1 (not thread_1_1)))\n"
    "\n"
    "(assert (=> preserve_1_1 (= accu_1_1 accu_0_1)))\n"
    "(assert (=> preserve_1_1 (= mem_1_1 mem_0_1)))\n"
    "\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_0 stmt_1_1_0)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_1 stmt_1_1_1)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_2 stmt_1_1_2)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_3 stmt_1_1_3)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_4 stmt_1_1_4)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_5 stmt_1_1_5)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_6 stmt_1_1_6)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_7 stmt_1_1_7)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_8 stmt_1_1_8)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_9 stmt_1_1_9)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_10 stmt_1_1_10)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_11 stmt_1_1_11)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_12 stmt_1_1_12)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_13 stmt_1_1_13)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_14 stmt_1_1_14)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_15 stmt_1_1_15)))\n"
    "(assert (=> preserve_1_1 (= stmt_2_1_16 stmt_1_1_16)))\n"
    "\n"
    "(declare-fun preserve_1_2 () Bool)\n"
    "(assert (= preserve_1_2 (not thread_1_2)))\n"
    "\n"
    "(assert (=> preserve_1_2 (= accu_1_2 accu_0_2)))\n"
    "(assert (=> preserve_1_2 (= mem_1_2 mem_0_2)))\n"
    "\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_0 stmt_1_2_0)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_1 stmt_1_2_1)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_2 stmt_1_2_2)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_3 stmt_1_2_3)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_4 stmt_1_2_4)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_5 stmt_1_2_5)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_6 stmt_1_2_6)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_7 stmt_1_2_7)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_8 stmt_1_2_8)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_9 stmt_1_2_9)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_10 stmt_1_2_10)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_11 stmt_1_2_11)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_12 stmt_1_2_12)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_13 stmt_1_2_13)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_14 stmt_1_2_14)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_15 stmt_1_2_15)))\n"
    "(assert (=> preserve_1_2 (= stmt_2_2_16 stmt_1_2_16)))\n\n",
    encoder->formula.str());

  /* step == bound */
  reset_encoder(2, 2);

  encoder->add_state_preservation();

  ASSERT_EQ(
    "; state preservation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun preserve_2_0 () Bool)\n"
    "(assert (= preserve_2_0 (not thread_2_0)))\n"
    "\n"
    "(assert (=> preserve_2_0 (= accu_2_0 accu_1_0)))\n"
    "(assert (=> preserve_2_0 (= mem_2_0 mem_1_0)))\n"
    "\n"
    "(declare-fun preserve_2_1 () Bool)\n"
    "(assert (= preserve_2_1 (not thread_2_1)))\n"
    "\n"
    "(assert (=> preserve_2_1 (= accu_2_1 accu_1_1)))\n"
    "(assert (=> preserve_2_1 (= mem_2_1 mem_1_1)))\n"
    "\n"
    "(declare-fun preserve_2_2 () Bool)\n"
    "(assert (= preserve_2_2 (not thread_2_2)))\n"
    "\n"
    "(assert (=> preserve_2_2 (= accu_2_2 accu_1_2)))\n"
    "(assert (=> preserve_2_2 (= mem_2_2 mem_1_2)))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(2, 2);

  verbose = false;
  encoder->add_state_preservation();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun preserve_2_0 () Bool)\n"
    "(assert (= preserve_2_0 (not thread_2_0)))\n"
    "\n"
    "(assert (=> preserve_2_0 (= accu_2_0 accu_1_0)))\n"
    "(assert (=> preserve_2_0 (= mem_2_0 mem_1_0)))\n"
    "\n"
    "(declare-fun preserve_2_1 () Bool)\n"
    "(assert (= preserve_2_1 (not thread_2_1)))\n"
    "\n"
    "(assert (=> preserve_2_1 (= accu_2_1 accu_1_1)))\n"
    "(assert (=> preserve_2_1 (= mem_2_1 mem_1_1)))\n"
    "\n"
    "(declare-fun preserve_2_2 () Bool)\n"
    "(assert (= preserve_2_2 (not thread_2_2)))\n"
    "\n"
    "(assert (=> preserve_2_2 (= accu_2_2 accu_1_2)))\n"
    "(assert (=> preserve_2_2 (= mem_2_2 mem_1_2)))\n\n",
    encoder->formula.str());
}

// virtual void encode (void);
TEST_F(SMTLibEncoderRelationalTest, encode_check)
{
  /* concurrent increment using CHECK */
  programs->push_back(
    create_from_file<Program>("data/increment.check.thread.0.asm"));
  programs->push_back(
    create_from_file<Program>("data/increment.check.thread.n.asm"));

  encoder = make_shared<SMTLibEncoderRelational>(programs, 16);

  ifstream ifs("data/increment.check.relational.t2.k16.smt2");

  string expected;
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderRelationalTest, encode_cas)
{
  /* concurrent increment using CAS */
  programs->push_back(create_from_file<Program>("data/increment.cas.asm"));
  programs->push_back(create_from_file<Program>("data/increment.cas.asm"));

  encoder = make_shared<SMTLibEncoderRelational>(programs, 16);

  ifstream ifs("data/increment.cas.relational.t2.k16.smt2");

  string expected;
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ASSERT_EQ(expected, encoder->formula.str());
}

// virtual std::string encode (Load &);
TEST_F(SMTLibEncoderRelationalTest, LOAD)
{
  add_dummy_programs(1);

  Load load = Load(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(load));

  /* indirect */
  load.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (select heap_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(load));
}

// virtual std::string encode (Store &);
TEST_F(SMTLibEncoderRelationalTest, STORE)
{
  add_dummy_programs(1);

  Store store = Store(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 (store heap_0 #x0001 accu_0_0))))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(store));

  /* indirect */
  store.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(= heap_1 (store heap_0 (select heap_0 #x0001) accu_0_0))))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(store));
}

// virtual std::string encode (Add &);
TEST_F(SMTLibEncoderRelationalTest, ADD)
{
  add_dummy_programs(1);

  Add add = Add(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvadd accu_0_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(add));

  /* indirect */
  add.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvadd accu_0_0 (select heap_0 (select heap_0 #x0001))))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(add));
}

// virtual std::string encode (Addi &);
TEST_F(SMTLibEncoderRelationalTest, ADDI)
{
  add_dummy_programs(1);

  Addi addi = Addi(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvadd accu_0_0 #x0001))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(addi));
}

// virtual std::string encode (Sub &);
TEST_F(SMTLibEncoderRelationalTest, SUB)
{
  add_dummy_programs(1);

  Sub sub = Sub(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvsub accu_0_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(sub));

  /* indirect */
  sub.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvsub accu_0_0 (select heap_0 (select heap_0 #x0001))))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(sub));
}

// virtual std::string encode (Subi &);
TEST_F(SMTLibEncoderRelationalTest, SUBI)
{
  add_dummy_programs(1);

  Subi subi = Subi(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvsub accu_0_0 #x0001))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(subi));
}

// virtual std::string encode (Cmp &);
TEST_F(SMTLibEncoderRelationalTest, CMP)
{
  add_dummy_programs(1);

  Cmp cmp = Cmp(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvsub accu_0_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(cmp));

  /* indirect */
  cmp.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (bvsub accu_0_0 (select heap_0 (select heap_0 #x0001))))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(cmp));
}

// virtual std::string encode (Jmp &);
TEST_F(SMTLibEncoderRelationalTest, JMP)
{
  add_dummy_programs(1);

  Jmp jmp = Jmp(2);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "(not stmt_2_0_1) "
        "stmt_2_0_2)"
    "))\n",
    encoder->encode(jmp));
}

// virtual std::string encode (Jz &);
TEST_F(SMTLibEncoderRelationalTest, JZ)
{
  add_dummy_programs(1);

  Jz jz = Jz(2);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(ite (= accu_1_0 #x0000) "
        "(and "
          "(not stmt_2_0_0) "
          "(not stmt_2_0_1) "
          "stmt_2_0_2) "
        "(and "
          "(not stmt_2_0_0) "
          "stmt_2_0_1 "
          "(not stmt_2_0_2))"
    ")))\n",
    encoder->encode(jz));
}

// virtual std::string encode (Jnz &);
TEST_F(SMTLibEncoderRelationalTest, JNZ)
{
  add_dummy_programs(1);

  Jnz jnz = Jnz(2);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(ite (not (= accu_1_0 #x0000)) "
        "(and "
          "(not stmt_2_0_0) "
          "(not stmt_2_0_1) "
          "stmt_2_0_2) "
        "(and "
          "(not stmt_2_0_0) "
          "stmt_2_0_1 "
          "(not stmt_2_0_2))"
    ")))\n",
    encoder->encode(jnz));
}

// virtual std::string encode (Js &);
TEST_F(SMTLibEncoderRelationalTest, JS)
{
  add_dummy_programs(1);

  Js js = Js(2);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(ite (= #b1 ((_ extract 15 15) accu_1_0)) "
        "(and "
          "(not stmt_2_0_0) "
          "(not stmt_2_0_1) "
          "stmt_2_0_2) "
        "(and "
          "(not stmt_2_0_0) "
          "stmt_2_0_1 "
          "(not stmt_2_0_2))"
    ")))\n",
    encoder->encode(js));
}

// virtual std::string encode (Jns &);
TEST_F(SMTLibEncoderRelationalTest, JNS)
{
  add_dummy_programs(1);

  Jns jns = Jns(2);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(ite (= #b0 ((_ extract 15 15) accu_1_0)) "
        "(and "
          "(not stmt_2_0_0) "
          "(not stmt_2_0_1) "
          "stmt_2_0_2) "
        "(and "
          "(not stmt_2_0_0) "
          "stmt_2_0_1 "
          "(not stmt_2_0_2))"
    ")))\n",
    encoder->encode(jns));
}

// virtual std::string encode (Jnzns &);
TEST_F(SMTLibEncoderRelationalTest, JNZNS)
{
  add_dummy_programs(1);

  Jnzns jnzns = Jnzns(2);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(ite "
        "(and (not (= accu_1_0 #x0000)) (= #b0 ((_ extract 15 15) accu_1_0))) "
        "(and "
          "(not stmt_2_0_0) "
          "(not stmt_2_0_1) "
          "stmt_2_0_2) "
        "(and "
          "(not stmt_2_0_0) "
          "stmt_2_0_1 "
          "(not stmt_2_0_2))"
    ")))\n",
    encoder->encode(jnzns));
}

// virtual std::string encode (Mem &);
TEST_F(SMTLibEncoderRelationalTest, MEM)
{
  add_dummy_programs(1);

  Mem mem = Mem(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 (select heap_0 #x0001))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 accu_1_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(mem));

  /* indirect */
  mem.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 "
      "(= accu_1_0 (select heap_0 (select heap_0 #x0001)))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 accu_1_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(mem));
}

// virtual std::string encode (Cas &);
TEST_F(SMTLibEncoderRelationalTest, CAS)
{
  add_dummy_programs(1);

  Cas cas = Cas(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 "
      "(ite "
        "(= mem_0_0 (select heap_0 #x0001)) "
        "#x0001 "
        "#x0000))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 "
      "(ite (= mem_0_0 (select heap_0 #x0001)) "
        "(store heap_0 #x0001 accu_0_0) "
        "heap_0))))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(cas));

  /* indirect */
  cas.indirect = true;

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 "
      "(ite "
        "(= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
        "#x0001 "
        "#x0000))))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 "
      "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
        "(store heap_0 (select heap_0 #x0001) accu_0_0) "
        "heap_0))))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(cas));
}

// virtual std::string encode (Check & c);
TEST_F(SMTLibEncoderRelationalTest, CHECK)
{
  add_dummy_programs(1);

  Check check = Check(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 "
      "(and "
        "(not stmt_2_0_0) "
        "stmt_2_0_1 "
        "(not stmt_2_0_2))"
    "))\n",
    encoder->encode(check));
}

// virtual std::string encode (Exit &);
TEST_F(SMTLibEncoderRelationalTest, EXIT)
{
  add_dummy_programs(1);

  Exit exit = Exit(1);

  ASSERT_EQ(
    "(assert (=> exec_1_0_0 (= accu_1_0 accu_0_0)))\n"
    "(assert (=> exec_1_0_0 (= mem_1_0 mem_0_0)))\n"
    "(assert (=> exec_1_0_0 (= heap_1 heap_0)))\n"
    "(assert (=> exec_1_0_0 (= exit-code #x0001)))\n",
    encoder->encode(exit));
}
