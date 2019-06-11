#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"

using namespace std;

struct SMTLibEncoderFunctionalTest : public ::testing::Test
{
  Program_list                programs;
  SMTLibEncoderFunctional_ptr encoder = create_encoder();

  Program_ptr create_program (string code)
    {
      string path = "dummy.asm";
      istringstream inbuf {code};
      return make_shared<Program>(inbuf, path);
    }

  SMTLibEncoderFunctional_ptr create_encoder (const bound_t bound = 1)
    {
      SMTLibEncoderFunctional_ptr e =
        make_shared<SMTLibEncoderFunctional>(
          make_shared<Program_list>(programs),
          bound,
          false);

      e->step = bound;
      e->prev = bound - 1;

      return e;
    }

  void reset_encoder (const bound_t step = 0)
    {
      encoder = create_encoder(step);
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

/* SMTLibEncoderFunctional::define_accu ***************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_accu)
{
  add_instruction_set(3);

  // initial state
  encoder->define_accu();

  ASSERT_EQ(
    "; accu states - accu_<step>_<thread>\n"
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_accu();

  ASSERT_EQ(
    "; accu states - accu_<step>_<thread>\n"
    "(assert (= accu_1_0 "
      "(ite exec_0_0_0 " // LOAD
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001)) "
        "(ite exec_0_0_2 " // ADD
          "(bvadd "
            "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001))) "
          "(ite exec_0_0_3 " // ADDI
            "(bvadd accu_0_0 #x0001) "
            "(ite exec_0_0_4 " // SUB
              "(bvsub "
                "accu_0_0 "
                "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
                  "sb-val_0_0 "
                  "(select heap_0 #x0001))) "
              "(ite exec_0_0_5 " // SUBI
                "(bvsub accu_0_0 #x0001) "
                "(ite exec_0_0_6 " // CMP
                  "(bvsub "
                    "accu_0_0 "
                    "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
                      "sb-val_0_0 "
                      "(select heap_0 #x0001))) "
                  "(ite exec_0_0_13 " // MEM
                    "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
                      "sb-val_0_0 "
                      "(select heap_0 #x0001)) "
                    "(ite exec_0_0_14 " // CAS
                      "(ite (= mem_0_0 (select heap_0 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_0_0))))))))))\n"
    "(assert (= accu_1_1 "
      "(ite exec_0_1_0 " // LOAD
        "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
          "sb-val_0_1 "
          "(select heap_0 #x0001)) "
        "(ite exec_0_1_2 " // ADD
          "(bvadd "
            "accu_0_1 "
            "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
              "sb-val_0_1 "
              "(select heap_0 #x0001))) "
          "(ite exec_0_1_3 " // ADDI
            "(bvadd accu_0_1 #x0001) "
            "(ite exec_0_1_4 " // SUB
              "(bvsub "
                "accu_0_1 "
                "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
                  "sb-val_0_1 "
                  "(select heap_0 #x0001))) "
              "(ite exec_0_1_5 " // SUBI
                "(bvsub accu_0_1 #x0001) "
                "(ite exec_0_1_6 " // CMP
                  "(bvsub "
                    "accu_0_1 "
                    "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
                      "sb-val_0_1 "
                      "(select heap_0 #x0001))) "
                  "(ite exec_0_1_13 " // MEM
                    "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
                      "sb-val_0_1 "
                      "(select heap_0 #x0001)) "
                    "(ite exec_0_1_14 " // CAS
                      "(ite (= mem_0_1 (select heap_0 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_0_1))))))))))\n"
    "(assert (= accu_1_2 "
      "(ite exec_0_2_0 " // LOAD
        "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
          "sb-val_0_2 "
          "(select heap_0 #x0001)) "
        "(ite exec_0_2_2 " // ADD
          "(bvadd "
            "accu_0_2 "
            "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
              "sb-val_0_2 "
              "(select heap_0 #x0001))) "
          "(ite exec_0_2_3 " // ADDI
            "(bvadd accu_0_2 #x0001) "
            "(ite exec_0_2_4 " // SUB
              "(bvsub "
                "accu_0_2 "
                "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
                  "sb-val_0_2 "
                  "(select heap_0 #x0001))) "
              "(ite exec_0_2_5 " // SUBI
                "(bvsub accu_0_2 #x0001) "
                "(ite exec_0_2_6 " // CMP
                  "(bvsub "
                    "accu_0_2 "
                    "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
                      "sb-val_0_2 "
                      "(select heap_0 #x0001))) "
                  "(ite exec_0_2_13 " // MEM
                    "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
                      "sb-val_0_2 "
                      "(select heap_0 #x0001)) "
                    "(ite exec_0_2_14 " // CAS
                      "(ite (= mem_0_2 (select heap_0 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_0_2))))))))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_accu();
  verbose = true;

  ASSERT_EQ(
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::define_mem ****************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_mem)
{
  add_instruction_set(3);

  // initial state
  encoder->define_mem();

  ASSERT_EQ(
    "; mem states - mem_<step>_<thread>\n"
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_mem();

  ASSERT_EQ(
    "; mem states - mem_<step>_<thread>\n"
    "(assert (= mem_1_0 "
      "(ite exec_0_0_13 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001)) "
        "mem_0_0)))\n"
    "(assert (= mem_1_1 "
      "(ite exec_0_1_13 "
        "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
          "sb-val_0_1 "
          "(select heap_0 #x0001)) "
        "mem_0_1)))\n"
    "(assert (= mem_1_2 "
      "(ite exec_0_2_13 "
        "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
          "sb-val_0_2 "
          "(select heap_0 #x0001)) "
        "mem_0_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_mem();
  verbose = true;

  ASSERT_EQ(
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::define_sb_adr *************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_sb_adr)
{
  add_instruction_set(3);

  // initial state
  encoder->define_sb_adr();

  ASSERT_EQ(
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_sb_adr();

  ASSERT_EQ(
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_1_0 (ite exec_0_0_1 #x0001 sb-adr_0_0)))\n"
    "(assert (= sb-adr_1_1 (ite exec_0_1_1 #x0001 sb-adr_0_1)))\n"
    "(assert (= sb-adr_1_2 (ite exec_0_2_1 #x0001 sb-adr_0_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_sb_adr();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::define_sb_val *************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_sb_val)
{
  add_instruction_set(3);

  // initial state
  encoder->define_sb_val();

  ASSERT_EQ(
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_sb_val();

  ASSERT_EQ(
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_1_0 (ite exec_0_0_1 accu_0_0 sb-val_0_0)))\n"
    "(assert (= sb-val_1_1 (ite exec_0_1_1 accu_0_1 sb-val_0_1)))\n"
    "(assert (= sb-val_1_2 (ite exec_0_2_1 accu_0_2 sb-val_0_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_sb_val();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::define_sb_full ************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_sb_full)
{
  add_instruction_set(3);

  // initial state
  encoder->define_sb_full();

  ASSERT_EQ(
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(assert (not sb-full_0_0))\n"
    "(assert (not sb-full_0_1))\n"
    "(assert (not sb-full_0_2))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_sb_full();

  ASSERT_EQ(
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(assert (= sb-full_1_0 (ite flush_0_0 false (or exec_0_0_1 sb-full_0_0))))\n"
    "(assert (= sb-full_1_1 (ite flush_0_1 false (or exec_0_1_1 sb-full_0_1))))\n"
    "(assert (= sb-full_1_2 (ite flush_0_2 false (or exec_0_2_1 sb-full_0_2))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_sb_full();
  verbose = true;

  ASSERT_EQ(
    "(assert (not sb-full_0_0))\n"
    "(assert (not sb-full_0_1))\n"
    "(assert (not sb-full_0_2))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_stmt)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
    ));

  reset_encoder();

  // initial step
  encoder->define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert stmt_0_0_0)\n"
    "(assert (not stmt_0_0_1))\n"
    "\n"
    "(assert stmt_0_1_0)\n"
    "(assert (not stmt_0_1_1))\n"
    "\n"
    "(assert stmt_0_2_0)\n"
    "(assert (not stmt_0_2_1))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(and stmt_0_0_1 (not exec_0_0_1)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(and stmt_0_1_1 (not exec_0_1_1)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(and stmt_0_2_1 (not exec_0_2_1)))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_stmt();
  verbose = true;

  ASSERT_EQ(
    "(assert stmt_0_0_0)\n"
    "(assert (not stmt_0_0_1))\n"
    "\n"
    "(assert stmt_0_1_0)\n"
    "(assert (not stmt_0_1_1))\n"
    "\n"
    "(assert stmt_0_2_0)\n"
    "(assert (not stmt_0_2_1))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_stmt_jmp)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JMP 1\n"
    ));

  reset_encoder(1);

  encoder->define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(ite stmt_0_0_2 "
          "exec_0_0_2 "
          "(and stmt_0_0_1 (not exec_0_0_1))))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(ite stmt_0_1_2 "
          "exec_0_1_2 "
          "(and stmt_0_1_1 (not exec_0_1_1))))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(ite stmt_0_2_2 "
          "exec_0_2_2 "
          "(and stmt_0_2_1 (not exec_0_2_1))))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_stmt_jmp_conditional)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JNZ 1\n"
      "EXIT 1\n"
    ));

  reset_encoder(1);

  encoder->define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(ite stmt_0_0_2 "
          "(and exec_0_0_2 (not (= accu_0_0 #x0000))) "
          "(and stmt_0_0_1 (not exec_0_0_1))))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "(assert (= stmt_1_0_3 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (not (= accu_0_0 #x0000)))) "
        "(and stmt_0_0_3 (not exec_0_0_3)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(ite stmt_0_1_2 "
          "(and exec_0_1_2 (not (= accu_0_1 #x0000))) "
          "(and stmt_0_1_1 (not exec_0_1_1))))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "(assert (= stmt_1_1_3 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (not (= accu_0_1 #x0000)))) "
        "(and stmt_0_1_3 (not exec_0_1_3)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(ite stmt_0_2_2 "
          "(and exec_0_2_2 (not (= accu_0_2 #x0000))) "
          "(and stmt_0_2_1 (not exec_0_2_1))))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "(assert (= stmt_1_2_3 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (not (= accu_0_2 #x0000)))) "
        "(and stmt_0_2_3 (not exec_0_2_3)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_stmt_jmp_start)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JNZ 0\n"
      "EXIT 1\n"
    ));

  reset_encoder(1);

  encoder->define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (= accu_0_0 #x0000))) "
        "(and stmt_0_0_0 (not exec_0_0_0)))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(and stmt_0_0_1 (not exec_0_0_1)))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "(assert (= stmt_1_0_3 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (not (= accu_0_0 #x0000)))) "
        "(and stmt_0_0_3 (not exec_0_0_3)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (= accu_0_1 #x0000))) "
        "(and stmt_0_1_0 (not exec_0_1_0)))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(and stmt_0_1_1 (not exec_0_1_1)))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "(assert (= stmt_1_1_3 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (not (= accu_0_1 #x0000)))) "
        "(and stmt_0_1_3 (not exec_0_1_3)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (= accu_0_2 #x0000))) "
        "(and stmt_0_2_0 (not exec_0_2_0)))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(and stmt_0_2_1 (not exec_0_2_1)))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "(assert (= stmt_1_2_3 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (not (= accu_0_2 #x0000)))) "
        "(and stmt_0_2_3 (not exec_0_2_3)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_stmt_jmp_twice)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JZ 1\n"
      "JNZ 1\n"
      "EXIT 1\n"
    ));

  reset_encoder(1);

  encoder->define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(ite stmt_0_0_2 "
          "(and exec_0_0_2 (= accu_0_0 #x0000)) "
          "(ite stmt_0_0_3 "
            "(and exec_0_0_3 (not (= accu_0_0 #x0000))) "
            "(and stmt_0_0_1 (not exec_0_0_1)))))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "(assert (= stmt_1_0_3 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (= accu_0_0 #x0000))) "
        "(and stmt_0_0_3 (not exec_0_0_3)))))\n"
    "(assert (= stmt_1_0_4 "
      "(ite stmt_0_0_3 "
        "(and exec_0_0_3 (not (not (= accu_0_0 #x0000)))) "
        "(and stmt_0_0_4 (not exec_0_0_4)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(ite stmt_0_1_2 "
          "(and exec_0_1_2 (= accu_0_1 #x0000)) "
          "(ite stmt_0_1_3 "
            "(and exec_0_1_3 (not (= accu_0_1 #x0000))) "
            "(and stmt_0_1_1 (not exec_0_1_1)))))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "(assert (= stmt_1_1_3 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (= accu_0_1 #x0000))) "
        "(and stmt_0_1_3 (not exec_0_1_3)))))\n"
    "(assert (= stmt_1_1_4 "
      "(ite stmt_0_1_3 "
        "(and exec_0_1_3 (not (not (= accu_0_1 #x0000)))) "
        "(and stmt_0_1_4 (not exec_0_1_4)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(ite stmt_0_2_2 "
          "(and exec_0_2_2 (= accu_0_2 #x0000)) "
          "(ite stmt_0_2_3 "
            "(and exec_0_2_3 (not (= accu_0_2 #x0000))) "
            "(and stmt_0_2_1 (not exec_0_2_1)))))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "(assert (= stmt_1_2_3 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (= accu_0_2 #x0000))) "
        "(and stmt_0_2_3 (not exec_0_2_3)))))\n"
    "(assert (= stmt_1_2_4 "
      "(ite stmt_0_2_3 "
        "(and exec_0_2_3 (not (not (= accu_0_2 #x0000)))) "
        "(and stmt_0_2_4 (not exec_0_2_4)))))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::define_block **************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_block)
{
  add_instruction_set(3);

  // initial step
  encoder->define_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(assert (not block_0_1_0))\n"
    "(assert (not block_0_1_1))\n"
    "(assert (not block_0_1_2))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(assert (= block_1_1_0 (ite check_0_1 false (or exec_0_0_15 block_0_1_0))))\n"
    "(assert (= block_1_1_1 (ite check_0_1 false (or exec_0_1_15 block_0_1_1))))\n"
    "(assert (= block_1_1_2 (ite check_0_1 false (or exec_0_2_15 block_0_1_2))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_block();
  verbose = true;

  ASSERT_EQ(
    "(assert (not block_0_1_0))\n"
    "(assert (not block_0_1_1))\n"
    "(assert (not block_0_1_2))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_block_no_check)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("ADDI " + to_string(i)));

  reset_encoder();

  encoder->define_block();

  ASSERT_EQ("", encoder->str());
}

/* SMTLibEncoderFunctional::define_heap ***************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_heap)
{
  add_instruction_set(3);

  // initial step
  encoder->define_heap();

  ASSERT_EQ("", encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_heap();

  ASSERT_EQ(
    "; heap state - heap_<step>\n"
    "(assert (= heap_1 "
      "(ite flush_0_0 " // FLUSH
        "(store heap_0 sb-adr_0_0 sb-val_0_0) "
        "(ite exec_0_0_14 " // CAS
          "(ite (= mem_0_0 (select heap_0 #x0001)) "
            "(store heap_0 #x0001 accu_0_0) "
            "heap_0) "
          "(ite flush_0_1 " // FLUSH
            "(store heap_0 sb-adr_0_1 sb-val_0_1) "
            "(ite exec_0_1_14 " // CAS
              "(ite (= mem_0_1 (select heap_0 #x0001)) "
                "(store heap_0 #x0001 accu_0_1) "
                "heap_0) "
              "(ite flush_0_2 " // FLUSH
                "(store heap_0 sb-adr_0_2 sb-val_0_2) "
                "(ite exec_0_2_14 " // CAS
                  "(ite (= mem_0_2 (select heap_0 #x0001)) "
                    "(store heap_0 #x0001 accu_0_2) "
                    "heap_0) "
                  "heap_0))))))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(1);

  verbose = false;
  encoder->define_heap();
  verbose = true;

  ASSERT_EQ(
    "(assert (= heap_1 "
      "(ite flush_0_0 " // FLUSH
        "(store heap_0 sb-adr_0_0 sb-val_0_0) "
        "(ite exec_0_0_14 " // CAS
          "(ite (= mem_0_0 (select heap_0 #x0001)) "
            "(store heap_0 #x0001 accu_0_0) "
            "heap_0) "
          "(ite flush_0_1 " // FLUSH
            "(store heap_0 sb-adr_0_1 sb-val_0_1) "
            "(ite exec_0_1_14 " // CAS
              "(ite (= mem_0_1 (select heap_0 #x0001)) "
                "(store heap_0 #x0001 accu_0_1) "
                "heap_0) "
              "(ite flush_0_2 " // FLUSH
                "(store heap_0 sb-adr_0_2 sb-val_0_2) "
                "(ite exec_0_2_14 " // CAS
                  "(ite (= mem_0_2 (select heap_0 #x0001)) "
                    "(store heap_0 #x0001 accu_0_2) "
                    "heap_0) "
                  "heap_0))))))))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::define_exit ***************************************/
TEST_F(SMTLibEncoderFunctionalTest, define_exit)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("EXIT " + to_string(i) + "\n"));

  // initial step
  reset_encoder();

  encoder->define_exit();

  ASSERT_EQ(
    "; exit flag - exit_<step>\n"
    "(assert (not exit_0))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_exit();

  ASSERT_EQ(
    "; exit flag - exit_<step>\n"
    "(assert (= exit_1 (or exit_0 exec_0_0_0 exec_0_1_0 exec_0_2_0)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_exit();
  verbose = true;

  ASSERT_EQ("(assert (not exit_0))\n\n", encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_exit_no_exit)
{
  encoder->define_exit();
  ASSERT_EQ("", encoder->str());
}

/* SMTLibEncoderFunctional::define_exit_code **********************************/
TEST_F(SMTLibEncoderFunctionalTest, define_exit_code)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("EXIT " + to_string(i)));

  // bound = step = 0
  reset_encoder();

  encoder->define_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (= exit-code #x0000))\n",
    encoder->str());

  // bound = step = 1
  reset_encoder(1);

  encoder->define_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (= exit-code "
      "(ite exec_1_0_0 "
        "#x0000 "
        "(ite exec_1_1_0 "
          "#x0001 "
          "(ite exec_1_2_0 "
            "#x0002 "
            "#x0000)))))\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_exit_code();
  verbose = true;

  ASSERT_EQ(
    "(assert (= exit-code #x0000))\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, define_exit_code_no_exit)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("ADDI " + to_string(i)));

  reset_encoder(1);

  encoder->define_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (= exit-code #x0000))\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::encode ********************************************/
TEST_F(SMTLibEncoderFunctionalTest, encode_check)
{
  // concurrent increment using CHECK
  programs.push_back(
    create_from_file<Program>("data/increment.check.thread.0.asm"));
  programs.push_back(
    create_from_file<Program>("data/increment.check.thread.n.asm"));

  encoder =
    make_shared<SMTLibEncoderFunctional>(
      make_shared<Program_list>(programs),
      16);

  ifstream ifs("data/increment.check.functional.t2.k16.smt2");

  string expected;
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ofstream tmp("/tmp/increment.check.functional.t2.k16.smt2");
  tmp << encoder->str();

  ASSERT_EQ(expected, encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, encode_cas)
{
  // concurrent increment using CAS
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));

  encoder =
    make_shared<SMTLibEncoderFunctional>(
      make_shared<Program_list>(programs),
      16);

  ifstream ifs("data/increment.cas.functional.t2.k16.smt2");

  string expected;
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ofstream tmp("/tmp/increment.cas.functional.t2.k16.smt2");
  tmp << encoder->str();

  ASSERT_EQ(expected, encoder->str());
}
