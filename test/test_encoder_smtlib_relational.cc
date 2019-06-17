#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "smtlib.hh"

using namespace std;

struct SMTLibEncoderRelationalTest : public ::testing::Test
{
  Program_list                programs;
  SMTLibEncoderRelational_ptr encoder = create_encoder();

  Program_ptr create_program (string code)
    {
      string path = "dummy.asm";
      istringstream inbuf {code};
      return make_shared<Program>(inbuf, path);
    }

  SMTLibEncoderRelational_ptr create_encoder (const bound_t bound = 1)
    {
      SMTLibEncoderRelational_ptr e =
        make_shared<SMTLibEncoderRelational>(
          make_shared<Program_list>(programs),
          bound,
          false);

      e->step = bound;
      e->prev = bound - 1;

      e->thread = 0;
      e->pc = 0;
      e->state = *e;

      return e;
    }

  void reset_encoder (const bound_t step = 1)
    {
      encoder = create_encoder(step);
    }

  void add_dummy_programs (unsigned num, unsigned size = 1)
    {
      ostringstream code;
      const char * op = "ADDI 1\n";

      for (size_t i = 0; i < size; i++)
        code << op;

      for (size_t i = 0; i < num; i++)
        programs.push_back(create_program(code.str()));

      encoder = create_encoder();
    }

  void add_instruction_set (unsigned num)
    {
      for (size_t i = 0; i < num; i++)
        programs.push_back(create_program(
          "LOAD 1\n"  // 0
          "STORE 1\n" // 1
          "ADD 1\n"   // 2
          "ADDI 1\n"  // 3
          "SUB 1\n"   // 4
          "SUBI 1\n"  // 5
          "CMP 1\n"   // 6
          "JMP 8\n"   // 7
          "JZ 1\n"    // 8
          "JNZ 1\n"   // 9
          "JS 1\n"    // 10
          "JNS 1\n"   // 11
          "JNZNS 1\n" // 12
          "MEM 1\n"   // 13
          "CAS 1\n"   // 14
          "CHECK 1\n" // 15
          "EXIT 1\n"  // 16
        ));

      reset_encoder();
    }
};

/* SMTLibEncoderRelational::imply *********************************************/
TEST_F(SMTLibEncoderRelationalTest, imply)
{
  ASSERT_EQ("(assert (=> foo bar))\n", encoder->imply("foo", "bar"));
}

/* SMTLibEncoderRelational::imply_thread_executed *****************************/
TEST_F(SMTLibEncoderRelationalTest, imply_thread_executed)
{
  programs.push_back(
    create_program(
      "ADDI 1\n"
      "CHECK 0\n"
      "EXIT 1\n"));

  reset_encoder();

  encoder->imply_thread_executed();

  ASSERT_EQ(
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 (bvadd accu_0_0 #x0001)) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and "
          "(not stmt_1_0_0) "
          "stmt_1_0_1 "
          "(not stmt_1_0_2)) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)) "
        "(= heap_1 heap_0) "
        "(not exit_1))))\n"
    "\n"
    "(assert (=> exec_0_0_1 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and "
          "(not stmt_1_0_0) "
          "(not stmt_1_0_1) "
          "stmt_1_0_2) "
        "block_1_0_0 "
        "(= heap_1 heap_0) "
        "(not exit_1))))\n"
    "\n"
    "(assert (=> exec_0_0_2 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and "
          "(not stmt_1_0_0) "
          "(not stmt_1_0_1) "
          "stmt_1_0_2) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)) "
        "(= heap_1 heap_0) "
        "exit_1 "
        "(= exit-code #x0001))))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderRelational::imply_thread_not_executed *************************/
TEST_F(SMTLibEncoderRelationalTest, imply_thread_not_executed)
{
  programs.push_back(
    create_program(
      "ADDI 1\n"
      "CHECK 0\n"
      "EXIT 1\n"));

  reset_encoder();

  encoder->imply_thread_not_executed();

  ASSERT_EQ(
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(and "
          "(= stmt_1_0_0 stmt_0_0_0) "
          "(= stmt_1_0_1 stmt_0_0_1) "
          "(= stmt_1_0_2 stmt_0_0_2)) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)))))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderRelational::imply_thread_flushed ******************************/
TEST_F(SMTLibEncoderRelationalTest, imply_thread_flushed)
{
  add_instruction_set(1);

  encoder->imply_thread_flushed();

  ASSERT_EQ(
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)) "
        "(not exit_1))))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderRelational::imply_machine_exited ******************************/
TEST_F(SMTLibEncoderRelationalTest, imply_machine_exited)
{
  add_instruction_set(1);

  encoder->imply_machine_exited();

  ASSERT_EQ(
    "; exited\n"
    "(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))\n"
    "\n"
    "(assert (=> (not exit_1) (= exit-code #x0000)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderRelational::define_states *************************************/
TEST_F(SMTLibEncoderRelationalTest, define_states)
{
  programs.push_back(create_program("JMP 0\n"));

  reset_encoder();

  encoder->define_states();

  ASSERT_EQ(
    "; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread 0\n"
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "stmt_1_0_0 "
        "(= heap_1 heap_0))))\n"
    "\n"
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(= stmt_1_0_0 stmt_0_0_0))))\n"
    "\n"
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_states();
  verbose = true;

  ASSERT_EQ(
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "stmt_1_0_0 "
        "(= heap_1 heap_0))))\n"
    "\n"
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(= stmt_1_0_0 stmt_0_0_0))))\n"
    "\n"
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderRelationalTest, define_states_check_exit)
{
  programs.push_back(
    create_program(
      "CHECK 0\n"
      "EXIT 1\n"
    ));

  reset_encoder();

  encoder->define_states();

  ASSERT_EQ(
    "; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread 0\n"
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and (not stmt_1_0_0) stmt_1_0_1) "
        "block_1_0_0 "
        "(= heap_1 heap_0) "
        "(not exit_1))))\n"
    "\n"
    "(assert (=> exec_0_0_1 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and (not stmt_1_0_0) stmt_1_0_1) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)) "
        "(= heap_1 heap_0) "
        "exit_1 "
        "(= exit-code #x0001))))\n"
    "\n"
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(and (= stmt_1_0_0 stmt_0_0_0) (= stmt_1_0_1 stmt_0_0_1)) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)))))\n"
    "\n"
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)) "
        "(not exit_1))))\n"
    "\n"
    "; exited\n"
    "(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))\n"
    "\n"
    "(assert (=> (not exit_1) (= exit-code #x0000)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderRelational::encode ********************************************/
TEST_F(SMTLibEncoderRelationalTest, encode_check)
{
  /* concurrent increment using CHECK */
  programs.push_back(
    create_from_file<Program>("data/increment.check.thread.0.asm"));
  programs.push_back(
    create_from_file<Program>("data/increment.check.thread.n.asm"));

  encoder =
    make_shared<SMTLibEncoderRelational>(
      make_shared<Program_list>(programs),
      16);

  ifstream ifs("data/increment.check.relational.t2.k16.smt2");

  string expected;
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ofstream tmp("/tmp/increment.check.relational.t2.k16.smt2");
  tmp << encoder->str();

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderRelationalTest, encode_cas)
{
  /* concurrent increment using CAS */
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));

  encoder =
    make_shared<SMTLibEncoderRelational>(
      make_shared<Program_list>(programs),
      16);

  ifstream ifs("data/increment.cas.relational.t2.k16.smt2");

  string expected;
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ofstream tmp("/tmp/increment.cas.relational.t2.k16.smt2");
  tmp << encoder->str();

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderRelationalTest, LOAD)
{
  add_instruction_set(1);

  Load load {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "stmt_1_0_1 "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(load));
}

TEST_F(SMTLibEncoderRelationalTest, LOAD_indirect)
{
  add_instruction_set(1);

  Load load {1, true};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite sb-full_0_0 "
          "(ite (= sb-adr_0_0 #x0001) "
            "(ite (= sb-val_0_0 #x0001) "
              "sb-val_0_0 "
              "(ite (= sb-adr_0_0 (select heap_0 sb-val_0_0)) "
                "sb-val_0_0 "
                "(select heap_0 (select heap_0 sb-val_0_0)))) "
            "(ite (= sb-adr_0_0 (select heap_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 (select heap_0 #x0001)))) "
          "(select heap_0 (select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "stmt_1_0_1 "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(load));
}

TEST_F(SMTLibEncoderRelationalTest, STORE)
{
  add_instruction_set(1);

  encoder->pc = 1;

  Store store {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 #x0001) "
      "(= sb-val_1_0 accu_0_0) "
      "sb-full_1_0 "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "stmt_1_0_2 "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(store));
}

TEST_F(SMTLibEncoderRelationalTest, STORE_indirect)
{
  add_instruction_set(1);

  encoder->pc = 1;

  Store store {1, true};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
        "sb-val_0_0 "
        "(select heap_0 #x0001))) "
      "(= sb-val_1_0 accu_0_0) "
      "sb-full_1_0 "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "stmt_1_0_2 "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(store));
}

TEST_F(SMTLibEncoderRelationalTest, ADD)
{
  add_instruction_set(1);

  encoder->pc = 2;

  Add add {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvadd "
          "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "stmt_1_0_3 "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(add));
}

TEST_F(SMTLibEncoderRelationalTest, ADD_indirect)
{
  add_instruction_set(1);

  encoder->pc = 2;

  Add add {1, true};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvadd "
          "accu_0_0 "
          "(ite sb-full_0_0 "
            "(ite (= sb-adr_0_0 #x0001) "
              "(ite (= sb-val_0_0 #x0001) "
                "sb-val_0_0 "
                "(ite (= sb-adr_0_0 (select heap_0 sb-val_0_0)) "
                  "sb-val_0_0 "
                  "(select heap_0 (select heap_0 sb-val_0_0)))) "
              "(ite (= sb-adr_0_0 (select heap_0 #x0001)) "
                "sb-val_0_0 "
                "(select heap_0 (select heap_0 #x0001)))) "
            "(select heap_0 (select heap_0 #x0001))))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "stmt_1_0_3 "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(add));
}

TEST_F(SMTLibEncoderRelationalTest, ADDI)
{
  add_instruction_set(1);

  encoder->pc = 3;

  Addi addi {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvadd accu_0_0 #x0001)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "stmt_1_0_4 "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(addi));
}

TEST_F(SMTLibEncoderRelationalTest, SUB)
{
  add_instruction_set(1);

  encoder->pc = 4;

  Sub sub {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "stmt_1_0_5 "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(sub));
}

TEST_F(SMTLibEncoderRelationalTest, SUB_indirect)
{
  add_instruction_set(1);

  encoder->pc = 4;

  Sub sub {1, true};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
          "(ite sb-full_0_0 "
            "(ite (= sb-adr_0_0 #x0001) "
              "(ite (= sb-val_0_0 #x0001) "
                "sb-val_0_0 "
                "(ite (= sb-adr_0_0 (select heap_0 sb-val_0_0)) "
                  "sb-val_0_0 "
                  "(select heap_0 (select heap_0 sb-val_0_0)))) "
              "(ite (= sb-adr_0_0 (select heap_0 #x0001)) "
                "sb-val_0_0 "
                "(select heap_0 (select heap_0 #x0001)))) "
            "(select heap_0 (select heap_0 #x0001))))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "stmt_1_0_5 "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(sub));
}

TEST_F(SMTLibEncoderRelationalTest, SUBI)
{
  add_instruction_set(1);

  encoder->pc = 5;

  Subi subi {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvsub accu_0_0 #x0001)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "stmt_1_0_6 "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(subi));
}

TEST_F(SMTLibEncoderRelationalTest, CMP)
{
  add_instruction_set(1);

  encoder->pc = 6;

  Cmp cmp {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "stmt_1_0_7 "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(cmp));
}

TEST_F(SMTLibEncoderRelationalTest, CMP_indirect)
{
  add_instruction_set(1);

  encoder->pc = 6;

  Cmp cmp {1, true};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
          "(ite sb-full_0_0 "
            "(ite (= sb-adr_0_0 #x0001) "
              "(ite (= sb-val_0_0 #x0001) "
                "sb-val_0_0 "
                "(ite (= sb-adr_0_0 (select heap_0 sb-val_0_0)) "
                  "sb-val_0_0 "
                  "(select heap_0 (select heap_0 sb-val_0_0)))) "
              "(ite (= sb-adr_0_0 (select heap_0 #x0001)) "
                "sb-val_0_0 "
                "(select heap_0 (select heap_0 #x0001)))) "
            "(select heap_0 (select heap_0 #x0001))))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "stmt_1_0_7 "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(cmp));
}

TEST_F(SMTLibEncoderRelationalTest, JMP)
{
  add_instruction_set(1);

  encoder->pc = 7;

  Jmp jmp {8};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "stmt_1_0_8 "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jmp));
}

TEST_F(SMTLibEncoderRelationalTest, JZ)
{
  add_instruction_set(1);

  encoder->pc = 8;

  Jz jz {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (= accu_0_0 #x0000) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(ite (= accu_0_0 #x0000) "
          "(not stmt_1_0_9) "
          "stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jz));
}

TEST_F(SMTLibEncoderRelationalTest, JNZ)
{
  add_instruction_set(1);

  encoder->pc = 9;

  Jnz jnz {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (not (= accu_0_0 #x0000)) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(ite (not (= accu_0_0 #x0000)) "
          "(not stmt_1_0_10) "
          "stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jnz));
}

TEST_F(SMTLibEncoderRelationalTest, JS)
{
  add_instruction_set(1);

  encoder->pc = 10;

  Js js {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (= #b1 ((_ extract 15 15) accu_0_0)) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(ite (= #b1 ((_ extract 15 15) accu_0_0)) "
          "(not stmt_1_0_11) "
          "stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(js));
}

TEST_F(SMTLibEncoderRelationalTest, JNS)
{
  add_instruction_set(1);

  encoder->pc = 11;

  Jns jns {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (= #b0 ((_ extract 15 15) accu_0_0)) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(ite (= #b0 ((_ extract 15 15) accu_0_0)) "
          "(not stmt_1_0_12) "
          "stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jns));
}

TEST_F(SMTLibEncoderRelationalTest, JNZNS)
{
  add_instruction_set(1);

  encoder->pc = 12;

  Jnzns jnzns {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite "
          "(and "
            "(not (= accu_0_0 #x0000)) "
            "(= #b0 ((_ extract 15 15) accu_0_0))) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(ite "
          "(and "
            "(not (= accu_0_0 #x0000)) "
            "(= #b0 ((_ extract 15 15) accu_0_0))) "
          "(not stmt_1_0_13) "
          "stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jnzns));
}

TEST_F(SMTLibEncoderRelationalTest, MEM)
{
  add_instruction_set(1);

  encoder->pc = 13;

  Mem mem {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001))) "
      "(= mem_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001))) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "stmt_1_0_14 "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(mem));
}

TEST_F(SMTLibEncoderRelationalTest, MEM_indirect)
{
  add_instruction_set(1);

  encoder->pc = 13;

  Mem mem {1, true};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite sb-full_0_0 "
          "(ite (= sb-adr_0_0 #x0001) "
            "(ite (= sb-val_0_0 #x0001) "
              "sb-val_0_0 "
              "(ite (= sb-adr_0_0 (select heap_0 sb-val_0_0)) "
                "sb-val_0_0 "
                "(select heap_0 (select heap_0 sb-val_0_0)))) "
            "(ite (= sb-adr_0_0 (select heap_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 (select heap_0 #x0001)))) "
          "(select heap_0 (select heap_0 #x0001)))) "
      "(= mem_1_0 "
        "(ite sb-full_0_0 "
          "(ite (= sb-adr_0_0 #x0001) "
            "(ite (= sb-val_0_0 #x0001) "
              "sb-val_0_0 "
              "(ite (= sb-adr_0_0 (select heap_0 sb-val_0_0)) "
                "sb-val_0_0 "
                "(select heap_0 (select heap_0 sb-val_0_0)))) "
            "(ite (= sb-adr_0_0 (select heap_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 (select heap_0 #x0001)))) "
          "(select heap_0 (select heap_0 #x0001)))) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "stmt_1_0_14 "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(mem));
}

TEST_F(SMTLibEncoderRelationalTest, CAS)
{
  add_instruction_set(1);

  encoder->pc = 14;

  Cas cas {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (= mem_0_0 (select heap_0 #x0001)) "
          "#x0001 "
          "#x0000)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "stmt_1_0_15 "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 "
        "(ite (= mem_0_0 (select heap_0 #x0001)) "
          "(store heap_0 #x0001 accu_0_0) "
          "heap_0)) "
      "(not exit_1))",
    encoder->encode(cas));
}

TEST_F(SMTLibEncoderRelationalTest, CAS_indirect)
{
  add_instruction_set(1);

  encoder->pc = 14;

  Cas cas {1, true};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
          "#x0001 "
          "#x0000)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "stmt_1_0_15 "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 "
        "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
          "(store heap_0 (select heap_0 #x0001) accu_0_0) "
          "heap_0)) "
      "(not exit_1))",
    encoder->encode(cas));
}

TEST_F(SMTLibEncoderRelationalTest, CHECK)
{
  add_instruction_set(1);

  encoder->pc = 15;

  Check check {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "stmt_1_0_16) "
      "block_1_1_0 "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(check));
}

TEST_F(SMTLibEncoderRelationalTest, HALT)
{
  // TODO
}

TEST_F(SMTLibEncoderRelationalTest, EXIT)
{
  add_instruction_set(1);

  encoder->pc = 16;

  Exit exit {1};

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "stmt_1_0_16) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "exit_1 "
      "(= exit-code #x0001))",
    encoder->encode(exit));
}
