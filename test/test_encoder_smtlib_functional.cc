#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"

using namespace std;

struct SMTLibEncoderFunctionalTest : public ::testing::Test
{
  Program_list_ptr            programs {make_shared<Program_list>()};
  SMTLibEncoderFunctional_ptr encoder {create_encoder(2, 2)};

  Program_ptr create_program (string code)
    {
      string path = "dummy.asm";
      istringstream inbuf {code};
      return make_shared<Program>(inbuf, path);
    }

  SMTLibEncoderFunctional_ptr create_encoder (word_t bound, word_t step)
    {
      SMTLibEncoderFunctional_ptr e =
        make_shared<SMTLibEncoderFunctional>(programs, bound, false);

      e->step = step;
      e->prev = step - 1u;

      return e;
    }

  void reset_encoder (const word_t bound, bound_t step)
    {
      encoder = create_encoder(bound, step);
    }

  void add_instruction_set (unsigned num)
    {
      for (size_t i = 0; i < num; i++)
        programs->push_back(create_program(
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

      reset_encoder(2, 2);
    }
};

/* SMTLibEncoderFunctional::add_statement_activation **************************/
TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation)
{
  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
    ));

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_2_0_0 () Bool)\n"
    "(declare-fun stmt_2_0_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "\n"
    "(assert (= stmt_2_0_0 (and stmt_1_0_0 (not exec_1_0_0))))\n"
    "(assert (= stmt_2_0_1 "
      "(ite stmt_1_0_0 "
        "exec_1_0_0 "
        "(and stmt_1_0_1 (not exec_1_0_1)))))\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 "
      "(ite stmt_1_1_0 "
        "exec_1_1_0 "
        "(and stmt_1_1_1 (not exec_1_1_1)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 "
      "(ite stmt_1_2_0 "
        "exec_1_2_0 "
        "(and stmt_1_2_1 (not exec_1_2_1)))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 2);

  verbose = false;
  encoder->add_statement_activation();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun stmt_2_0_0 () Bool)\n"
    "(declare-fun stmt_2_0_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "\n"
    "(assert (= stmt_2_0_0 (and stmt_1_0_0 (not exec_1_0_0))))\n"
    "(assert (= stmt_2_0_1 "
      "(ite stmt_1_0_0 "
        "exec_1_0_0 "
        "(and stmt_1_0_1 (not exec_1_0_1)))))\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 "
      "(ite stmt_1_1_0 "
        "exec_1_1_0 "
        "(and stmt_1_1_1 (not exec_1_1_1)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 "
      "(ite stmt_1_2_0 "
        "exec_1_2_0 "
        "(and stmt_1_2_1 (not exec_1_2_1)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp)
{
  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JMP 1\n"
    ));

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
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
    "(declare-fun stmt_2_2_2 () Bool)\n"
    "\n"
    "(assert (= stmt_2_0_0 (and stmt_1_0_0 (not exec_1_0_0))))\n"
    "(assert (= stmt_2_0_1 "
      "(ite stmt_1_0_0 "
        "exec_1_0_0 "
        "(ite stmt_1_0_2 "
          "exec_1_0_2 "
          "(and stmt_1_0_1 (not exec_1_0_1))))))\n"
    "(assert (= stmt_2_0_2 "
      "(ite stmt_1_0_1 "
        "exec_1_0_1 "
        "(and stmt_1_0_2 (not exec_1_0_2)))))\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 "
      "(ite stmt_1_1_0 "
        "exec_1_1_0 "
        "(ite stmt_1_1_2 "
          "exec_1_1_2 "
          "(and stmt_1_1_1 (not exec_1_1_1))))))\n"
    "(assert (= stmt_2_1_2 "
      "(ite stmt_1_1_1 "
        "exec_1_1_1 "
        "(and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 "
      "(ite stmt_1_2_0 "
        "exec_1_2_0 "
        "(ite stmt_1_2_2 "
          "exec_1_2_2 "
          "(and stmt_1_2_1 (not exec_1_2_1))))))\n"
    "(assert (= stmt_2_2_2 "
      "(ite stmt_1_2_1 "
        "exec_1_2_1 "
        "(and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_conditional)
{
  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JNZ 1\n"
      "EXIT 1\n"
    ));

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_2_0_0 () Bool)\n"
    "(declare-fun stmt_2_0_1 () Bool)\n"
    "(declare-fun stmt_2_0_2 () Bool)\n"
    "(declare-fun stmt_2_0_3 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "(declare-fun stmt_2_1_2 () Bool)\n"
    "(declare-fun stmt_2_1_3 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "(declare-fun stmt_2_2_2 () Bool)\n"
    "(declare-fun stmt_2_2_3 () Bool)\n"
    "\n"
    "(assert (= stmt_2_0_0 (and stmt_1_0_0 (not exec_1_0_0))))\n"
    "(assert (= stmt_2_0_1 "
      "(ite stmt_1_0_0 "
        "exec_1_0_0 "
        "(ite stmt_1_0_2 "
          "(and exec_1_0_2 (not (= accu_1_0 #x0000))) "
          "(and stmt_1_0_1 (not exec_1_0_1))))))\n"
    "(assert (= stmt_2_0_2 "
      "(ite stmt_1_0_1 "
        "exec_1_0_1 "
        "(and stmt_1_0_2 (not exec_1_0_2)))))\n"
    "(assert (= stmt_2_0_3 "
      "(ite stmt_1_0_2 "
        "(and exec_1_0_2 (not (not (= accu_1_0 #x0000)))) "
        "(and stmt_1_0_3 (not exec_1_0_3)))))\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 "
      "(ite stmt_1_1_0 "
        "exec_1_1_0 "
        "(ite stmt_1_1_2 "
          "(and exec_1_1_2 (not (= accu_1_1 #x0000))) "
          "(and stmt_1_1_1 (not exec_1_1_1))))))\n"
    "(assert (= stmt_2_1_2 "
      "(ite stmt_1_1_1 "
        "exec_1_1_1 "
        "(and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "(assert (= stmt_2_1_3 "
      "(ite stmt_1_1_2 "
        "(and exec_1_1_2 (not (not (= accu_1_1 #x0000)))) "
        "(and stmt_1_1_3 (not exec_1_1_3)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 "
      "(ite stmt_1_2_0 "
        "exec_1_2_0 "
        "(ite stmt_1_2_2 "
          "(and exec_1_2_2 (not (= accu_1_2 #x0000))) "
          "(and stmt_1_2_1 (not exec_1_2_1))))))\n"
    "(assert (= stmt_2_2_2 "
      "(ite stmt_1_2_1 "
        "exec_1_2_1 "
        "(and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "(assert (= stmt_2_2_3 "
      "(ite stmt_1_2_2 "
        "(and exec_1_2_2 (not (not (= accu_1_2 #x0000)))) "
        "(and stmt_1_2_3 (not exec_1_2_3)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_start)
{
  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JNZ 0\n"
      "EXIT 1\n"
    ));

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_2_0_0 () Bool)\n"
    "(declare-fun stmt_2_0_1 () Bool)\n"
    "(declare-fun stmt_2_0_2 () Bool)\n"
    "(declare-fun stmt_2_0_3 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "(declare-fun stmt_2_1_2 () Bool)\n"
    "(declare-fun stmt_2_1_3 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "(declare-fun stmt_2_2_2 () Bool)\n"
    "(declare-fun stmt_2_2_3 () Bool)\n"
    "\n"
    "(assert (= stmt_2_0_0 "
      "(ite stmt_1_0_2 "
        "(and exec_1_0_2 (not (= accu_1_0 #x0000))) "
        "(and stmt_1_0_0 (not exec_1_0_0)))))\n"
    "(assert (= stmt_2_0_1 "
      "(ite stmt_1_0_0 "
        "exec_1_0_0 "
        "(and stmt_1_0_1 (not exec_1_0_1)))))\n"
    "(assert (= stmt_2_0_2 "
      "(ite stmt_1_0_1 "
        "exec_1_0_1 "
        "(and stmt_1_0_2 (not exec_1_0_2)))))\n"
    "(assert (= stmt_2_0_3 "
      "(ite stmt_1_0_2 "
        "(and exec_1_0_2 (not (not (= accu_1_0 #x0000)))) "
        "(and stmt_1_0_3 (not exec_1_0_3)))))\n"
    "\n"
    "(assert (= stmt_2_1_0 "
      "(ite stmt_1_1_2 "
        "(and exec_1_1_2 (not (= accu_1_1 #x0000))) "
        "(and stmt_1_1_0 (not exec_1_1_0)))))\n"
    "(assert (= stmt_2_1_1 "
      "(ite stmt_1_1_0 "
        "exec_1_1_0 "
        "(and stmt_1_1_1 (not exec_1_1_1)))))\n"
    "(assert (= stmt_2_1_2 "
      "(ite stmt_1_1_1 "
        "exec_1_1_1 "
        "(and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "(assert (= stmt_2_1_3 "
      "(ite stmt_1_1_2 "
        "(and exec_1_1_2 (not (not (= accu_1_1 #x0000)))) "
        "(and stmt_1_1_3 (not exec_1_1_3)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 "
      "(ite stmt_1_2_2 "
        "(and exec_1_2_2 (not (= accu_1_2 #x0000))) "
        "(and stmt_1_2_0 (not exec_1_2_0)))))\n"
    "(assert (= stmt_2_2_1 "
      "(ite stmt_1_2_0 "
        "exec_1_2_0 "
        "(and stmt_1_2_1 (not exec_1_2_1)))))\n"
    "(assert (= stmt_2_2_2 "
      "(ite stmt_1_2_1 "
        "exec_1_2_1 "
        "(and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "(assert (= stmt_2_2_3 "
      "(ite stmt_1_2_2 "
        "(and exec_1_2_2 (not (not (= accu_1_2 #x0000)))) "
        "(and stmt_1_2_3 (not exec_1_2_3)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_twice)
{
  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program(
      "ADDI 1\n"
      "STORE 1\n"
      "JZ 1\n"
      "JNZ 1\n"
      "EXIT 1\n"
    ));

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  ASSERT_EQ(
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_2_0_0 () Bool)\n"
    "(declare-fun stmt_2_0_1 () Bool)\n"
    "(declare-fun stmt_2_0_2 () Bool)\n"
    "(declare-fun stmt_2_0_3 () Bool)\n"
    "(declare-fun stmt_2_0_4 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "(declare-fun stmt_2_1_2 () Bool)\n"
    "(declare-fun stmt_2_1_3 () Bool)\n"
    "(declare-fun stmt_2_1_4 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "(declare-fun stmt_2_2_2 () Bool)\n"
    "(declare-fun stmt_2_2_3 () Bool)\n"
    "(declare-fun stmt_2_2_4 () Bool)\n"
    "\n"
    "(assert (= stmt_2_0_0 (and stmt_1_0_0 (not exec_1_0_0))))\n"
    "(assert (= stmt_2_0_1 "
      "(ite stmt_1_0_0 "
        "exec_1_0_0 "
        "(ite stmt_1_0_2 "
          "(and exec_1_0_2 (= accu_1_0 #x0000)) "
          "(ite stmt_1_0_3 "
            "(and exec_1_0_3 (not (= accu_1_0 #x0000))) "
            "(and stmt_1_0_1 (not exec_1_0_1)))))))\n"
    "(assert (= stmt_2_0_2 "
      "(ite stmt_1_0_1 "
        "exec_1_0_1 "
        "(and stmt_1_0_2 (not exec_1_0_2)))))\n"
    "(assert (= stmt_2_0_3 "
      "(ite stmt_1_0_2 "
        "(and exec_1_0_2 (not (= accu_1_0 #x0000))) "
        "(and stmt_1_0_3 (not exec_1_0_3)))))\n"
    "(assert (= stmt_2_0_4 "
      "(ite stmt_1_0_3 "
        "(and exec_1_0_3 (not (not (= accu_1_0 #x0000)))) "
        "(and stmt_1_0_4 (not exec_1_0_4)))))\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 "
      "(ite stmt_1_1_0 "
        "exec_1_1_0 "
        "(ite stmt_1_1_2 "
          "(and exec_1_1_2 (= accu_1_1 #x0000)) "
          "(ite stmt_1_1_3 "
            "(and exec_1_1_3 (not (= accu_1_1 #x0000))) "
            "(and stmt_1_1_1 (not exec_1_1_1)))))))\n"
    "(assert (= stmt_2_1_2 "
      "(ite stmt_1_1_1 "
        "exec_1_1_1 "
        "(and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "(assert (= stmt_2_1_3 "
      "(ite stmt_1_1_2 "
        "(and exec_1_1_2 (not (= accu_1_1 #x0000))) "
        "(and stmt_1_1_3 (not exec_1_1_3)))))\n"
    "(assert (= stmt_2_1_4 "
      "(ite stmt_1_1_3 "
        "(and exec_1_1_3 (not (not (= accu_1_1 #x0000)))) "
        "(and stmt_1_1_4 (not exec_1_1_4)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 "
      "(ite stmt_1_2_0 "
        "exec_1_2_0 "
        "(ite stmt_1_2_2 "
          "(and exec_1_2_2 (= accu_1_2 #x0000)) "
          "(ite stmt_1_2_3 "
            "(and exec_1_2_3 (not (= accu_1_2 #x0000))) "
            "(and stmt_1_2_1 (not exec_1_2_1)))))))\n"
    "(assert (= stmt_2_2_2 "
      "(ite stmt_1_2_1 "
        "exec_1_2_1 "
        "(and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "(assert (= stmt_2_2_3 "
      "(ite stmt_1_2_2 "
        "(and exec_1_2_2 (not (= accu_1_2 #x0000))) "
        "(and stmt_1_2_3 (not exec_1_2_3)))))\n"
    "(assert (= stmt_2_2_4 "
      "(ite stmt_1_2_3 "
        "(and exec_1_2_3 (not (not (= accu_1_2 #x0000)))) "
        "(and stmt_1_2_4 (not exec_1_2_4)))))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::add_state_updates *********************************/
TEST_F(SMTLibEncoderFunctionalTest, add_state_updates)
{
  add_instruction_set(3);

  encoder->add_state_updates();

  ASSERT_EQ(
    "; state updates ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_2_0 () (_ BitVec 16))\n"
    "(declare-fun accu_2_1 () (_ BitVec 16))\n"
    "(declare-fun accu_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_2_0 "
      "(ite exec_2_0_0 " // LOAD
        "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
          "sb-val_1_0 "
          "(select heap_1 #x0001)) "
        "(ite exec_2_0_2 " // ADD
          "(bvadd "
            "accu_1_0 "
            "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
              "sb-val_1_0 "
              "(select heap_1 #x0001))) "
          "(ite exec_2_0_3 " // ADDI
            "(bvadd accu_1_0 #x0001) "
            "(ite exec_2_0_4 " // SUB
              "(bvsub "
                "accu_1_0 "
                "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
                  "sb-val_1_0 "
                  "(select heap_1 #x0001))) "
              "(ite exec_2_0_5 " // SUBI
                "(bvsub accu_1_0 #x0001) "
                "(ite exec_2_0_6 " // CMP
                  "(bvsub "
                    "accu_1_0 "
                    "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
                      "sb-val_1_0 "
                      "(select heap_1 #x0001))) "
                  "(ite exec_2_0_13 " // MEM
                    "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
                      "sb-val_1_0 "
                      "(select heap_1 #x0001)) "
                    "(ite exec_2_0_14 " // CAS
                      "(ite (= mem_1_0 (select heap_1 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_1_0))))))))))\n"
    "(assert (= accu_2_1 "
      "(ite exec_2_1_0 " // LOAD
        "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
          "sb-val_1_1 "
          "(select heap_1 #x0001)) "
        "(ite exec_2_1_2 " // ADD
          "(bvadd "
            "accu_1_1 "
            "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
              "sb-val_1_1 "
              "(select heap_1 #x0001))) "
          "(ite exec_2_1_3 " // ADDI
            "(bvadd accu_1_1 #x0001) "
            "(ite exec_2_1_4 " // SUB
              "(bvsub "
                "accu_1_1 "
                "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
                  "sb-val_1_1 "
                  "(select heap_1 #x0001))) "
              "(ite exec_2_1_5 " // SUBI
                "(bvsub accu_1_1 #x0001) "
                "(ite exec_2_1_6 " // CMP
                  "(bvsub "
                    "accu_1_1 "
                    "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
                      "sb-val_1_1 "
                      "(select heap_1 #x0001))) "
                  "(ite exec_2_1_13 " // MEM
                    "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
                      "sb-val_1_1 "
                      "(select heap_1 #x0001)) "
                    "(ite exec_2_1_14 " // CAS
                      "(ite (= mem_1_1 (select heap_1 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_1_1))))))))))\n"
    "(assert (= accu_2_2 "
      "(ite exec_2_2_0 " // LOAD
        "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
          "sb-val_1_2 "
          "(select heap_1 #x0001)) "
        "(ite exec_2_2_2 " // ADD
          "(bvadd "
            "accu_1_2 "
            "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
              "sb-val_1_2 "
              "(select heap_1 #x0001))) "
          "(ite exec_2_2_3 " // ADDI
            "(bvadd accu_1_2 #x0001) "
            "(ite exec_2_2_4 " // SUB
              "(bvsub "
                "accu_1_2 "
                "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
                  "sb-val_1_2 "
                  "(select heap_1 #x0001))) "
              "(ite exec_2_2_5 " // SUBI
                "(bvsub accu_1_2 #x0001) "
                "(ite exec_2_2_6 " // CMP
                  "(bvsub "
                    "accu_1_2 "
                    "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
                      "sb-val_1_2 "
                      "(select heap_1 #x0001))) "
                  "(ite exec_2_2_13 " // MEM
                    "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
                      "sb-val_1_2 "
                      "(select heap_1 #x0001)) "
                    "(ite exec_2_2_14 " // CAS
                      "(ite (= mem_1_2 (select heap_1 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_1_2))))))))))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_2_0 () (_ BitVec 16))\n"
    "(declare-fun mem_2_1 () (_ BitVec 16))\n"
    "(declare-fun mem_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_2_0 "
      "(ite exec_2_0_13 "
        "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
          "sb-val_1_0 "
          "(select heap_1 #x0001)) "
        "mem_1_0)))\n"
    "(assert (= mem_2_1 "
      "(ite exec_2_1_13 "
        "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
          "sb-val_1_1 "
          "(select heap_1 #x0001)) "
        "mem_1_1)))\n"
    "(assert (= mem_2_2 "
      "(ite exec_2_2_13 "
        "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
          "sb-val_1_2 "
          "(select heap_1 #x0001)) "
        "mem_1_2)))\n"
    "\n"
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_2_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_2_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_2_0 (ite exec_2_0_1 #x0001 sb-adr_1_0)))\n"
    "(assert (= sb-adr_2_1 (ite exec_2_1_1 #x0001 sb-adr_1_1)))\n"
    "(assert (= sb-adr_2_2 (ite exec_2_2_1 #x0001 sb-adr_1_2)))\n"
    "\n"
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_2_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_2_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_2_0 (ite exec_2_0_1 accu_1_0 sb-val_1_0)))\n"
    "(assert (= sb-val_2_1 (ite exec_2_1_1 accu_1_1 sb-val_1_1)))\n"
    "(assert (= sb-val_2_2 (ite exec_2_2_1 accu_1_2 sb-val_1_2)))\n"
    "\n"
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_2_0 () Bool)\n"
    "(declare-fun sb-full_2_1 () Bool)\n"
    "(declare-fun sb-full_2_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_2_0 (ite flush_2_0 false (or sb-full_1_0 exec_2_0_1))))\n"
    "(assert (= sb-full_2_1 (ite flush_2_1 false (or sb-full_1_1 exec_2_1_1))))\n"
    "(assert (= sb-full_2_2 (ite flush_2_2 false (or sb-full_1_2 exec_2_2_1))))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_2 "
      "(ite flush_2_0 " // FLUSH
        "(store heap_1 sb-adr_1_0 sb-val_1_0) "
        "(ite exec_2_0_14 " // CAS
          "(ite (= mem_1_0 (select heap_1 #x0001)) "
            "(store heap_1 #x0001 accu_1_0) "
            "heap_1) "
          "(ite flush_2_1 " // FLUSH
            "(store heap_1 sb-adr_1_1 sb-val_1_1) "
            "(ite exec_2_1_14 " // CAS
              "(ite (= mem_1_1 (select heap_1 #x0001)) "
                "(store heap_1 #x0001 accu_1_1) "
                "heap_1) "
              "(ite flush_2_2 " // FLUSH
                "(store heap_1 sb-adr_1_2 sb-val_1_2) "
                "(ite exec_2_2_14 " // CAS
                  "(ite (= mem_1_2 (select heap_1 #x0001)) "
                    "(store heap_1 #x0001 accu_1_2) "
                    "heap_1) "
                  "heap_1))))))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(2, 2);

  verbose = false;
  encoder->add_state_updates();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_2_0 () (_ BitVec 16))\n"
    "(declare-fun accu_2_1 () (_ BitVec 16))\n"
    "(declare-fun accu_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_2_0 "
      "(ite exec_2_0_0 " // LOAD
        "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
          "sb-val_1_0 "
          "(select heap_1 #x0001)) "
        "(ite exec_2_0_2 " // ADD
          "(bvadd "
            "accu_1_0 "
            "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
              "sb-val_1_0 "
              "(select heap_1 #x0001))) "
          "(ite exec_2_0_3 " // ADDI
            "(bvadd accu_1_0 #x0001) "
            "(ite exec_2_0_4 " // SUB
              "(bvsub "
                "accu_1_0 "
                "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
                  "sb-val_1_0 "
                  "(select heap_1 #x0001))) "
              "(ite exec_2_0_5 " // SUBI
                "(bvsub accu_1_0 #x0001) "
                "(ite exec_2_0_6 " // CMP
                  "(bvsub "
                    "accu_1_0 "
                    "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
                      "sb-val_1_0 "
                      "(select heap_1 #x0001))) "
                  "(ite exec_2_0_13 " // MEM
                    "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
                      "sb-val_1_0 "
                      "(select heap_1 #x0001)) "
                    "(ite exec_2_0_14 " // CAS
                      "(ite (= mem_1_0 (select heap_1 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_1_0))))))))))\n"
    "(assert (= accu_2_1 "
      "(ite exec_2_1_0 " // LOAD
        "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
          "sb-val_1_1 "
          "(select heap_1 #x0001)) "
        "(ite exec_2_1_2 " // ADD
          "(bvadd "
            "accu_1_1 "
            "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
              "sb-val_1_1 "
              "(select heap_1 #x0001))) "
          "(ite exec_2_1_3 " // ADDI
            "(bvadd accu_1_1 #x0001) "
            "(ite exec_2_1_4 " // SUB
              "(bvsub "
                "accu_1_1 "
                "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
                  "sb-val_1_1 "
                  "(select heap_1 #x0001))) "
              "(ite exec_2_1_5 " // SUBI
                "(bvsub accu_1_1 #x0001) "
                "(ite exec_2_1_6 " // CMP
                  "(bvsub "
                    "accu_1_1 "
                    "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
                      "sb-val_1_1 "
                      "(select heap_1 #x0001))) "
                  "(ite exec_2_1_13 " // MEM
                    "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
                      "sb-val_1_1 "
                      "(select heap_1 #x0001)) "
                    "(ite exec_2_1_14 " // CAS
                      "(ite (= mem_1_1 (select heap_1 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_1_1))))))))))\n"
    "(assert (= accu_2_2 "
      "(ite exec_2_2_0 " // LOAD
        "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
          "sb-val_1_2 "
          "(select heap_1 #x0001)) "
        "(ite exec_2_2_2 " // ADD
          "(bvadd "
            "accu_1_2 "
            "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
              "sb-val_1_2 "
              "(select heap_1 #x0001))) "
          "(ite exec_2_2_3 " // ADDI
            "(bvadd accu_1_2 #x0001) "
            "(ite exec_2_2_4 " // SUB
              "(bvsub "
                "accu_1_2 "
                "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
                  "sb-val_1_2 "
                  "(select heap_1 #x0001))) "
              "(ite exec_2_2_5 " // SUBI
                "(bvsub accu_1_2 #x0001) "
                "(ite exec_2_2_6 " // CMP
                  "(bvsub "
                    "accu_1_2 "
                    "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
                      "sb-val_1_2 "
                      "(select heap_1 #x0001))) "
                  "(ite exec_2_2_13 " // MEM
                    "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
                      "sb-val_1_2 "
                      "(select heap_1 #x0001)) "
                    "(ite exec_2_2_14 " // CAS
                      "(ite (= mem_1_2 (select heap_1 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_1_2))))))))))\n"
    "\n"
    "(declare-fun mem_2_0 () (_ BitVec 16))\n"
    "(declare-fun mem_2_1 () (_ BitVec 16))\n"
    "(declare-fun mem_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_2_0 "
      "(ite exec_2_0_13 "
        "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
          "sb-val_1_0 "
          "(select heap_1 #x0001)) "
        "mem_1_0)))\n"
    "(assert (= mem_2_1 "
      "(ite exec_2_1_13 "
        "(ite (and sb-full_1_1 (= sb-adr_1_1 #x0001)) "
          "sb-val_1_1 "
          "(select heap_1 #x0001)) "
        "mem_1_1)))\n"
    "(assert (= mem_2_2 "
      "(ite exec_2_2_13 "
        "(ite (and sb-full_1_2 (= sb-adr_1_2 #x0001)) "
          "sb-val_1_2 "
          "(select heap_1 #x0001)) "
        "mem_1_2)))\n"
    "\n"
    "(declare-fun sb-adr_2_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_2_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_2_0 (ite exec_2_0_1 #x0001 sb-adr_1_0)))\n"
    "(assert (= sb-adr_2_1 (ite exec_2_1_1 #x0001 sb-adr_1_1)))\n"
    "(assert (= sb-adr_2_2 (ite exec_2_2_1 #x0001 sb-adr_1_2)))\n"
    "\n"
    "(declare-fun sb-val_2_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_2_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_2_0 (ite exec_2_0_1 accu_1_0 sb-val_1_0)))\n"
    "(assert (= sb-val_2_1 (ite exec_2_1_1 accu_1_1 sb-val_1_1)))\n"
    "(assert (= sb-val_2_2 (ite exec_2_2_1 accu_1_2 sb-val_1_2)))\n"
    "\n"
    "(declare-fun sb-full_2_0 () Bool)\n"
    "(declare-fun sb-full_2_1 () Bool)\n"
    "(declare-fun sb-full_2_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_2_0 (ite flush_2_0 false (or sb-full_1_0 exec_2_0_1))))\n"
    "(assert (= sb-full_2_1 (ite flush_2_1 false (or sb-full_1_1 exec_2_1_1))))\n"
    "(assert (= sb-full_2_2 (ite flush_2_2 false (or sb-full_1_2 exec_2_2_1))))\n"
    "\n"
    "(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_2 "
      "(ite flush_2_0 " // FLUSH
        "(store heap_1 sb-adr_1_0 sb-val_1_0) "
        "(ite exec_2_0_14 " // CAS
          "(ite (= mem_1_0 (select heap_1 #x0001)) "
            "(store heap_1 #x0001 accu_1_0) "
            "heap_1) "
          "(ite flush_2_1 " // FLUSH
            "(store heap_1 sb-adr_1_1 sb-val_1_1) "
            "(ite exec_2_1_14 " // CAS
              "(ite (= mem_1_1 (select heap_1 #x0001)) "
                "(store heap_1 #x0001 accu_1_1) "
                "heap_1) "
              "(ite flush_2_2 " // FLUSH
                "(store heap_1 sb-adr_1_2 sb-val_1_2) "
                "(ite exec_2_2_14 " // CAS
                  "(ite (= mem_1_2 (select heap_1 #x0001)) "
                    "(store heap_1 #x0001 accu_1_2) "
                    "heap_1) "
                  "heap_1))))))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_state_updates_initial)
{
  add_instruction_set(3);

  encoder->step = 1;
  encoder->prev = 0;

  encoder->add_state_updates();

  ASSERT_EQ(
    "; state updates ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_1_0 "
      "(ite exec_1_0_0 " // LOAD
        "(select heap_0 #x0001) "
        "(ite exec_1_0_2 " // ADD
          "(bvadd accu_0_0 (select heap_0 #x0001)) "
          "(ite exec_1_0_3 " // ADDI
            "(bvadd accu_0_0 #x0001) "
            "(ite exec_1_0_4 " // SUB
              "(bvsub accu_0_0 (select heap_0 #x0001)) "
              "(ite exec_1_0_5 " // SUBI
                "(bvsub accu_0_0 #x0001) "
                "(ite exec_1_0_6 " // CMP
                  "(bvsub accu_0_0 (select heap_0 #x0001)) "
                  "(ite exec_1_0_13 " // MEM
                    "(select heap_0 #x0001) "
                    "(ite exec_1_0_14 " // CAS
                      "(ite (= mem_0_0 (select heap_0 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_0_0))))))))))\n"
    "(assert (= accu_1_1 "
      "(ite exec_1_1_0 " // LOAD
        "(select heap_0 #x0001) "
        "(ite exec_1_1_2 " // ADD
          "(bvadd accu_0_1 (select heap_0 #x0001)) "
          "(ite exec_1_1_3 " // ADDI
            "(bvadd accu_0_1 #x0001) "
            "(ite exec_1_1_4 " // SUB
              "(bvsub accu_0_1 (select heap_0 #x0001)) "
              "(ite exec_1_1_5 " // SUBI
                "(bvsub accu_0_1 #x0001) "
                "(ite exec_1_1_6 " // CMP
                  "(bvsub accu_0_1 (select heap_0 #x0001)) "
                  "(ite exec_1_1_13 " // MEM
                    "(select heap_0 #x0001) "
                    "(ite exec_1_1_14 " // CAS
                      "(ite (= mem_0_1 (select heap_0 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_0_1))))))))))\n"
    "(assert (= accu_1_2 "
      "(ite exec_1_2_0 " // LOAD
        "(select heap_0 #x0001) "
        "(ite exec_1_2_2 " // ADD
          "(bvadd accu_0_2 (select heap_0 #x0001)) "
          "(ite exec_1_2_3 " // ADDI
            "(bvadd accu_0_2 #x0001) "
            "(ite exec_1_2_4 " // SUB
              "(bvsub accu_0_2 (select heap_0 #x0001)) "
              "(ite exec_1_2_5 " // SUBI
                "(bvsub accu_0_2 #x0001) "
                "(ite exec_1_2_6 " // CMP
                  "(bvsub accu_0_2 (select heap_0 #x0001)) "
                  "(ite exec_1_2_13 " // MEM
                    "(select heap_0 #x0001) "
                    "(ite exec_1_2_14 " // CAS
                      "(ite (= mem_0_2 (select heap_0 #x0001)) "
                        "#x0001 "
                        "#x0000) "
                      "accu_0_2))))))))))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_1_0 (ite exec_1_0_13 (select heap_0 #x0001) mem_0_0)))\n"
    "(assert (= mem_1_1 (ite exec_1_1_13 (select heap_0 #x0001) mem_0_1)))\n"
    "(assert (= mem_1_2 (ite exec_1_2_13 (select heap_0 #x0001) mem_0_2)))\n"
    "\n"
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_1_0 (ite exec_1_0_1 #x0001 sb-adr_0_0)))\n"
    "(assert (= sb-adr_1_1 (ite exec_1_1_1 #x0001 sb-adr_0_1)))\n"
    "(assert (= sb-adr_1_2 (ite exec_1_2_1 #x0001 sb-adr_0_2)))\n"
    "\n"
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_1_0 (ite exec_1_0_1 accu_0_0 sb-val_0_0)))\n"
    "(assert (= sb-val_1_1 (ite exec_1_1_1 accu_0_1 sb-val_0_1)))\n"
    "(assert (= sb-val_1_2 (ite exec_1_2_1 accu_0_2 sb-val_0_2)))\n"
    "\n"
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_1_0 () Bool)\n"
    "(declare-fun sb-full_1_1 () Bool)\n"
    "(declare-fun sb-full_1_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_1_0 (or sb-full_0_0 exec_1_0_1)))\n"
    "(assert (= sb-full_1_1 (or sb-full_0_1 exec_1_1_1)))\n"
    "(assert (= sb-full_1_2 (or sb-full_0_2 exec_1_2_1)))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_1 "
        "(ite exec_1_0_14 " // CAS
          "(ite (= mem_0_0 (select heap_0 #x0001)) "
            "(store heap_0 #x0001 accu_0_0) "
            "heap_0) "
            "(ite exec_1_1_14 " // CAS
              "(ite (= mem_0_1 (select heap_0 #x0001)) "
                "(store heap_0 #x0001 accu_0_1) "
                "heap_0) "
                "(ite exec_1_2_14 " // CAS
                  "(ite (= mem_0_2 (select heap_0 #x0001)) "
                    "(store heap_0 #x0001 accu_0_2) "
                    "heap_0) "
                  "heap_0)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_state_updates_no_alteration)
{
  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program(
      "JMP 1\n"
      "JMP 0\n"
    ));

  reset_encoder(2, 2);

  encoder->add_state_updates();

  ASSERT_EQ(
    "; state updates ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_2_0 () (_ BitVec 16))\n"
    "(declare-fun accu_2_1 () (_ BitVec 16))\n"
    "(declare-fun accu_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_2_0 accu_1_0))\n"
    "(assert (= accu_2_1 accu_1_1))\n"
    "(assert (= accu_2_2 accu_1_2))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_2_0 () (_ BitVec 16))\n"
    "(declare-fun mem_2_1 () (_ BitVec 16))\n"
    "(declare-fun mem_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_2_0 mem_1_0))\n"
    "(assert (= mem_2_1 mem_1_1))\n"
    "(assert (= mem_2_2 mem_1_2))\n"
    "\n"
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_2_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_2_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_2_0 sb-adr_1_0))\n"
    "(assert (= sb-adr_2_1 sb-adr_1_1))\n"
    "(assert (= sb-adr_2_2 sb-adr_1_2))\n"
    "\n"
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_2_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_2_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_2_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_2_0 sb-val_1_0))\n"
    "(assert (= sb-val_2_1 sb-val_1_1))\n"
    "(assert (= sb-val_2_2 sb-val_1_2))\n"
    "\n"
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_2_0 () Bool)\n"
    "(declare-fun sb-full_2_1 () Bool)\n"
    "(declare-fun sb-full_2_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_2_0 (ite flush_2_0 false sb-full_1_0)))\n"
    "(assert (= sb-full_2_1 (ite flush_2_1 false sb-full_1_1)))\n"
    "(assert (= sb-full_2_2 (ite flush_2_2 false sb-full_1_2)))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_2 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_2 "
      "(ite flush_2_0 "
        "(store heap_1 sb-adr_1_0 sb-val_1_0) "
        "(ite flush_2_1 "
          "(store heap_1 sb-adr_1_1 sb-val_1_1) "
          "(ite flush_2_2 "
            "(store heap_1 sb-adr_1_2 sb-val_1_2) "
            "heap_1)))))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::add_exit_code *************************************/
TEST_F(SMTLibEncoderFunctionalTest, add_exit_code)
{
  // no call to EXIT
  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program("ADDI " + to_string(i)));

  encoder->add_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit-code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit-code #x0000))\n",
    encoder->str());

  // step 1
  programs->clear();

  for (size_t i = 0; i < 3; i++)
    programs->push_back(create_program("EXIT " + to_string(i)));

  reset_encoder(1, 1);

  encoder->add_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit-code () (_ BitVec 16))\n"
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

  // reached bound
  reset_encoder(3, 3);

  encoder->add_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit-code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit-code "
      "(ite exec_1_0_0 "
        "#x0000 "
        "(ite exec_1_1_0 "
          "#x0001 "
          "(ite exec_1_2_0 "
            "#x0002 "
            "(ite exec_2_0_0 "
              "#x0000 "
              "(ite exec_2_1_0 "
                "#x0001 "
                "(ite exec_2_2_0 "
                  "#x0002 "
                  "(ite exec_3_0_0 "
                    "#x0000 "
                    "(ite exec_3_1_0 "
                      "#x0001 "
                      "(ite exec_3_2_0 "
                        "#x0002 "
                        "#x0000)))))))))))\n",
    encoder->str());

  // verbosity
  reset_encoder(3, 3);

  verbose = false;
  encoder->add_exit_code();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun exit-code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit-code "
      "(ite exec_1_0_0 "
        "#x0000 "
        "(ite exec_1_1_0 "
          "#x0001 "
          "(ite exec_1_2_0 "
            "#x0002 "
            "(ite exec_2_0_0 "
              "#x0000 "
              "(ite exec_2_1_0 "
                "#x0001 "
                "(ite exec_2_2_0 "
                  "#x0002 "
                  "(ite exec_3_0_0 "
                    "#x0000 "
                    "(ite exec_3_1_0 "
                      "#x0001 "
                      "(ite exec_3_2_0 "
                        "#x0002 "
                        "#x0000)))))))))))\n",
    encoder->str());
}

/* SMTLibEncoderFunctional::encode ********************************************/
TEST_F(SMTLibEncoderFunctionalTest, encode_check)
{
  // concurrent increment using CHECK
  programs->push_back(
    create_from_file<Program>("data/increment.check.thread.0.asm"));
  programs->push_back(
    create_from_file<Program>("data/increment.check.thread.n.asm"));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

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
  programs->push_back(create_from_file<Program>("data/increment.cas.asm"));
  programs->push_back(create_from_file<Program>("data/increment.cas.asm"));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  ifstream ifs("data/increment.cas.functional.t2.k16.smt2");

  string expected;
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ofstream tmp("/tmp/increment.cas.functional.t2.k16.smt2");
  tmp << encoder->str();

  ASSERT_EQ(expected, encoder->str());
}

TEST_F(SMTLibEncoderFunctionalTest, LOAD)
{
  Load load = Load(1);

  ASSERT_EQ(
    "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
      "sb-val_1_0 "
      "(select heap_1 #x0001))",
    encoder->encode(load));

  // indirect
  load.indirect = true;

  ASSERT_EQ(
    "(ite "
      "(and "
        "sb-full_1_0 "
        "(= "
          "sb-adr_1_0 "
          "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
            "sb-val_1_0 "
            "(select heap_1 #x0001)))) "
      "sb-val_1_0 "
      "(select "
        "heap_1 "
        "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
          "sb-val_1_0 "
          "(select heap_1 #x0001))))",
    encoder->encode(load));
}

TEST_F(SMTLibEncoderFunctionalTest, STORE)
{
  Store store = Store(1);

  encoder->update = Encoder::Update::sb_adr;
  ASSERT_EQ("#x0001", encoder->encode(store));

  encoder->update = Encoder::Update::sb_val;
  ASSERT_EQ("accu_1_0", encoder->encode(store));

  // indirect
  store.indirect = true;

  encoder->update = Encoder::Update::sb_adr;
  ASSERT_EQ(
    "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
      "sb-val_1_0 "
      "(select heap_1 #x0001))",
    encoder->encode(store));

  encoder->update = Encoder::Update::sb_val;
  ASSERT_EQ("accu_1_0", encoder->encode(store));
}

TEST_F(SMTLibEncoderFunctionalTest, ADD)
{
  encoder->step = 2;
  encoder->prev = 1;

  Add add = Add(1);

  ASSERT_EQ(
    "(bvadd accu_1_0 "
      "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
        "sb-val_1_0 "
        "(select heap_1 #x0001)))",
    encoder->encode(add));

  // indirect
  add.indirect = true;

  ASSERT_EQ(
    "(bvadd accu_1_0 "
      "(ite "
        "(and "
          "sb-full_1_0 "
          "(= "
            "sb-adr_1_0 "
            "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
              "sb-val_1_0 "
              "(select heap_1 #x0001)))) "
        "sb-val_1_0 "
        "(select "
          "heap_1 "
          "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
            "sb-val_1_0 "
            "(select heap_1 #x0001)))))",
    encoder->encode(add));
}

TEST_F(SMTLibEncoderFunctionalTest, ADDI)
{
  Addi addi = Addi(1);

  ASSERT_EQ("(bvadd accu_1_0 #x0001)", encoder->encode(addi));
}

TEST_F(SMTLibEncoderFunctionalTest, SUB)
{
  Sub sub = Sub(1);

  ASSERT_EQ(
    "(bvsub accu_1_0 "
      "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
        "sb-val_1_0 "
        "(select heap_1 #x0001)))",
    encoder->encode(sub));

  // indirect
  sub.indirect = true;

  ASSERT_EQ(
    "(bvsub accu_1_0 "
      "(ite "
        "(and "
          "sb-full_1_0 "
          "(= "
            "sb-adr_1_0 "
            "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
              "sb-val_1_0 "
              "(select heap_1 #x0001)))) "
        "sb-val_1_0 "
        "(select "
          "heap_1 "
          "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
            "sb-val_1_0 "
            "(select heap_1 #x0001)))))",
    encoder->encode(sub));
}

TEST_F(SMTLibEncoderFunctionalTest, SUBI)
{
  Subi subi = Subi(1);

  ASSERT_EQ("(bvsub accu_1_0 #x0001)", encoder->encode(subi));
}

TEST_F(SMTLibEncoderFunctionalTest, CMP)
{
  Cmp cmp = Cmp(1);

  ASSERT_EQ(
    "(bvsub accu_1_0 "
      "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
        "sb-val_1_0 "
        "(select heap_1 #x0001)))",
    encoder->encode(cmp));

  // indirect
  cmp.indirect = true;

  ASSERT_EQ(
    "(bvsub accu_1_0 "
      "(ite "
        "(and "
          "sb-full_1_0 "
          "(= "
            "sb-adr_1_0 "
            "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
              "sb-val_1_0 "
              "(select heap_1 #x0001)))) "
        "sb-val_1_0 "
        "(select "
          "heap_1 "
          "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
            "sb-val_1_0 "
            "(select heap_1 #x0001)))))",
    encoder->encode(cmp));
}

TEST_F(SMTLibEncoderFunctionalTest, JMP)
{
  Jmp jmp = Jmp(1);

  ASSERT_TRUE(encoder->encode(jmp).empty());
}

TEST_F(SMTLibEncoderFunctionalTest, JZ)
{
  Jz jz = Jz(1);

  ASSERT_EQ("(= accu_1_0 #x0000)", encoder->encode(jz));
}

TEST_F(SMTLibEncoderFunctionalTest, JNZ)
{
  Jnz jnz = Jnz(1);

  ASSERT_EQ("(not (= accu_1_0 #x0000))", encoder->encode(jnz));
}

TEST_F(SMTLibEncoderFunctionalTest, JS)
{
  Js js = Js(1);

  ASSERT_EQ(
    "(= #b1 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_1_0))",
    encoder->encode(js));
}

TEST_F(SMTLibEncoderFunctionalTest, JNS)
{
  Jns jns = Jns(1);

  ASSERT_EQ(
    "(= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_1_0))",
    encoder->encode(jns));
}

TEST_F(SMTLibEncoderFunctionalTest, JNZNS)
{
  Jnzns jnzns = Jnzns(1);

  ASSERT_EQ(
    "(and (not (= accu_1_0 #x0000)) (= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") accu_1_0)))",
    encoder->encode(jnzns));
}

TEST_F(SMTLibEncoderFunctionalTest, MEM)
{
  Mem mem = Mem(1);

  ASSERT_EQ(
    "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
      "sb-val_1_0 "
      "(select heap_1 #x0001))",
    encoder->encode(mem));

  // indirect
  mem.indirect = true;

  ASSERT_EQ(
    "(ite "
      "(and "
        "sb-full_1_0 "
        "(= "
          "sb-adr_1_0 "
          "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
            "sb-val_1_0 "
            "(select heap_1 #x0001)))) "
      "sb-val_1_0 "
      "(select "
        "heap_1 "
        "(ite (and sb-full_1_0 (= sb-adr_1_0 #x0001)) "
          "sb-val_1_0 "
          "(select heap_1 #x0001))))",
    encoder->encode(mem));
}

TEST_F(SMTLibEncoderFunctionalTest, CAS)
{
  Cas cas = Cas(1);

  encoder->update = Encoder::Update::accu;

  ASSERT_EQ(
    "(ite "
      "(= mem_1_0 (select heap_1 #x0001)) "
      "#x0001 "
      "#x0000)",
    encoder->encode(cas));

  encoder->update = Encoder::Update::heap;

  ASSERT_EQ(
    "(ite "
      "(= mem_1_0 (select heap_1 #x0001)) "
      "(store heap_1 #x0001 accu_1_0) "
      "heap_1)",
    encoder->encode(cas));

  // indirect
  cas.indirect = true;

  encoder->update = Encoder::Update::accu;

  ASSERT_EQ(
    "(ite "
      "(= mem_1_0 (select heap_1 (select heap_1 #x0001))) "
      "#x0001 "
      "#x0000)",
    encoder->encode(cas));

  encoder->update = Encoder::Update::heap;

  ASSERT_EQ(
    "(ite "
      "(= mem_1_0 (select heap_1 (select heap_1 #x0001))) "
      "(store heap_1 (select heap_1 #x0001) accu_1_0) "
      "heap_1)",
    encoder->encode(cas));
}

TEST_F(SMTLibEncoderFunctionalTest, CHECK)
{
  Check check = Check(1);

  ASSERT_TRUE(encoder->encode(check).empty());
}

TEST_F(SMTLibEncoderFunctionalTest, EXIT)
{
  Exit exit = Exit(1);

  ASSERT_EQ("#x0001", encoder->encode(exit));
}
