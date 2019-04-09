#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"

using namespace std;

struct SMTLibEncoderFunctionalTest : public ::testing::Test
{
  string                      expected;
  ProgramList                 programs;
  SMTLibEncoderFunctionalPtr  encoder = create_encoder(1, 1);

  SMTLibEncoderFunctionalPtr create_encoder (const word bound, const word step)
    {
      SMTLibEncoderFunctionalPtr e =
        make_shared<SMTLibEncoderFunctional>(
          make_shared<ProgramList>(programs),
          bound,
          false);

      e->step = step;

      return e;
    }

  void reset_encoder (const word bound, unsigned long step)
    {
      encoder = create_encoder(bound, step);
    }

  void add_instruction_set (unsigned num)
    {
      for (size_t i = 0; i < num; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));

          programs[i]->push_back(Instruction::Set::create("LOAD", 1));  // 0
          programs[i]->push_back(Instruction::Set::create("STORE", 1)); // 1
          programs[i]->push_back(Instruction::Set::create("ADD", 1));   // 2
          programs[i]->push_back(Instruction::Set::create("ADDI", 1));  // 3
          programs[i]->push_back(Instruction::Set::create("SUB", 1));   // 4
          programs[i]->push_back(Instruction::Set::create("SUBI", 1));  // 5
          programs[i]->push_back(Instruction::Set::create("CMP", 1));   // 6
          programs[i]->push_back(Instruction::Set::create("JMP", 1));   // 7
          programs[i]->push_back(Instruction::Set::create("JZ", 1));    // 8
          programs[i]->push_back(Instruction::Set::create("JNZ", 1));   // 9
          programs[i]->push_back(Instruction::Set::create("JS", 1));    // 10
          programs[i]->push_back(Instruction::Set::create("JNS", 1));   // 11
          programs[i]->push_back(Instruction::Set::create("JNZNS", 1)); // 12
          programs[i]->push_back(Instruction::Set::create("MEM", 1));   // 13
          programs[i]->push_back(Instruction::Set::create("CAS", 1));   // 14
          programs[i]->push_back(Instruction::Set::create("SYNC", 1));  // 15
          programs[i]->push_back(Instruction::Set::create("EXIT", 1));  // 16
        }

      reset_encoder(1, 1);
    }
};

// SMTLibEncoderFunctional::SMTLibEncoderFunctional (
//                                                   const ProgramListPtr,
//                                                   unsigned long,
//                                                   bool
//                                                  );
TEST_F(SMTLibEncoderFunctionalTest, constructor)
{
  add_instruction_set(3);

  /* heap altering pcs */
  ASSERT_EQ(3, encoder->alters_heap.size());

  vector<word> alters_heap({1, 14});

  for (const auto & pcs: encoder->alters_heap)
    ASSERT_EQ(alters_heap, pcs.second);

  /* accu altering pcs */
  ASSERT_EQ(3, encoder->alters_accu.size());

  vector<word> alters_accu({0, 2, 3, 4, 5, 6, 13, 14});

  for (const auto & pcs: encoder->alters_accu)
    ASSERT_EQ(alters_accu, pcs.second);

  /* mem altering pcs */
  ASSERT_EQ(3, encoder->alters_mem.size());

  vector<word> alters_mem({13});

  for (const auto & pcs: encoder->alters_mem)
    ASSERT_EQ(alters_mem, pcs.second);
}

// void add_statement_activation (void);
TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_basic)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
    }

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  expected =
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_3_0 () Bool)\n"
    "(declare-fun stmt_2_3_1 () Bool)\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (and stmt_1_3_0 (not exec_1_3_0))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 2);

  verbose = false;
  encoder->add_statement_activation();
  verbose = true;

  expected =
    "(declare-fun stmt_2_1_0 () Bool)\n"
    "(declare-fun stmt_2_1_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_2_0 () Bool)\n"
    "(declare-fun stmt_2_2_1 () Bool)\n"
    "\n"
    "(declare-fun stmt_2_3_0 () Bool)\n"
    "(declare-fun stmt_2_3_1 () Bool)\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (and stmt_1_3_0 (not exec_1_3_0))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JMP", 1));
    }

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  expected =
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
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
    "(declare-fun stmt_2_3_2 () Bool)\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 (ite stmt_1_1_2 exec_1_1_2 (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1))))))\n"
    "(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_2 exec_1_2_2 (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1))))))\n"
    "(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (and stmt_1_3_0 (not exec_1_3_0))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_2 exec_1_3_2 (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1))))))\n"
    "(assert (= stmt_2_3_2 (ite stmt_1_3_1 exec_1_3_1 (and stmt_1_3_2 (not exec_1_3_2)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_conditional)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JNZ", 1));
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  expected =
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
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
    "(declare-fun stmt_2_3_0 () Bool)\n"
    "(declare-fun stmt_2_3_1 () Bool)\n"
    "(declare-fun stmt_2_3_2 () Bool)\n"
    "(declare-fun stmt_2_3_3 () Bool)\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 (ite stmt_1_1_2 (and exec_1_1_2 (not (= accu_1_1 #x0000))) (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1))))))\n"
    "(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "(assert (= stmt_2_1_3 (ite stmt_1_1_2 (and exec_1_1_2 (not (not (= accu_1_1 #x0000)))) (and stmt_1_1_3 (not exec_1_1_3)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_2 (and exec_1_2_2 (not (= accu_1_2 #x0000))) (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1))))))\n"
    "(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "(assert (= stmt_2_2_3 (ite stmt_1_2_2 (and exec_1_2_2 (not (not (= accu_1_2 #x0000)))) (and stmt_1_2_3 (not exec_1_2_3)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (and stmt_1_3_0 (not exec_1_3_0))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_2 (and exec_1_3_2 (not (= accu_1_3 #x0000))) (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1))))))\n"
    "(assert (= stmt_2_3_2 (ite stmt_1_3_1 exec_1_3_1 (and stmt_1_3_2 (not exec_1_3_2)))))\n"
    "(assert (= stmt_2_3_3 (ite stmt_1_3_2 (and exec_1_3_2 (not (not (= accu_1_3 #x0000)))) (and stmt_1_3_3 (not exec_1_3_3)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_start)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JNZ", 0));
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  expected =
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
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
    "(declare-fun stmt_2_3_0 () Bool)\n"
    "(declare-fun stmt_2_3_1 () Bool)\n"
    "(declare-fun stmt_2_3_2 () Bool)\n"
    "(declare-fun stmt_2_3_3 () Bool)\n"
    "\n"
    "(assert (= stmt_2_1_0 (ite stmt_1_1_2 (and exec_1_1_2 (not (= accu_1_1 #x0000))) (and stmt_1_1_0 (not exec_1_1_0)))))\n"
    "(assert (= stmt_2_1_1 (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1)))))\n"
    "(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "(assert (= stmt_2_1_3 (ite stmt_1_1_2 (and exec_1_1_2 (not (not (= accu_1_1 #x0000)))) (and stmt_1_1_3 (not exec_1_1_3)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (ite stmt_1_2_2 (and exec_1_2_2 (not (= accu_1_2 #x0000))) (and stmt_1_2_0 (not exec_1_2_0)))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1)))))\n"
    "(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "(assert (= stmt_2_2_3 (ite stmt_1_2_2 (and exec_1_2_2 (not (not (= accu_1_2 #x0000)))) (and stmt_1_2_3 (not exec_1_2_3)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (ite stmt_1_3_2 (and exec_1_3_2 (not (= accu_1_3 #x0000))) (and stmt_1_3_0 (not exec_1_3_0)))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1)))))\n"
    "(assert (= stmt_2_3_2 (ite stmt_1_3_1 exec_1_3_1 (and stmt_1_3_2 (not exec_1_3_2)))))\n"
    "(assert (= stmt_2_3_3 (ite stmt_1_3_2 (and exec_1_3_2 (not (not (= accu_1_3 #x0000)))) (and stmt_1_3_3 (not exec_1_3_3)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_twice)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("STORE", 1));
      programs[i]->push_back(Instruction::Set::create("JZ", 1));
      programs[i]->push_back(Instruction::Set::create("JNZ", 1));
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
    }

  reset_encoder(0, 2);

  encoder->add_statement_activation();

  expected =
    "; statement activation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
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
    "(declare-fun stmt_2_3_0 () Bool)\n"
    "(declare-fun stmt_2_3_1 () Bool)\n"
    "(declare-fun stmt_2_3_2 () Bool)\n"
    "(declare-fun stmt_2_3_3 () Bool)\n"
    "(declare-fun stmt_2_3_4 () Bool)\n"
    "\n"
    "(assert (= stmt_2_1_0 (and stmt_1_1_0 (not exec_1_1_0))))\n"
    "(assert (= stmt_2_1_1 (ite stmt_1_1_3 (and exec_1_1_3 (not (= accu_1_1 #x0000))) (ite stmt_1_1_2 (and exec_1_1_2 (= accu_1_1 #x0000)) (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1)))))))\n"
    "(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "(assert (= stmt_2_1_3 (ite stmt_1_1_2 (and exec_1_1_2 (not (= accu_1_1 #x0000))) (and stmt_1_1_3 (not exec_1_1_3)))))\n"
    "(assert (= stmt_2_1_4 (ite stmt_1_1_3 (and exec_1_1_3 (not (not (= accu_1_1 #x0000)))) (and stmt_1_1_4 (not exec_1_1_4)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_3 (and exec_1_2_3 (not (= accu_1_2 #x0000))) (ite stmt_1_2_2 (and exec_1_2_2 (= accu_1_2 #x0000)) (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1)))))))\n"
    "(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "(assert (= stmt_2_2_3 (ite stmt_1_2_2 (and exec_1_2_2 (not (= accu_1_2 #x0000))) (and stmt_1_2_3 (not exec_1_2_3)))))\n"
    "(assert (= stmt_2_2_4 (ite stmt_1_2_3 (and exec_1_2_3 (not (not (= accu_1_2 #x0000)))) (and stmt_1_2_4 (not exec_1_2_4)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (and stmt_1_3_0 (not exec_1_3_0))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_3 (and exec_1_3_3 (not (= accu_1_3 #x0000))) (ite stmt_1_3_2 (and exec_1_3_2 (= accu_1_3 #x0000)) (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1)))))))\n"
    "(assert (= stmt_2_3_2 (ite stmt_1_3_1 exec_1_3_1 (and stmt_1_3_2 (not exec_1_3_2)))))\n"
    "(assert (= stmt_2_3_3 (ite stmt_1_3_2 (and exec_1_3_2 (not (= accu_1_3 #x0000))) (and stmt_1_3_3 (not exec_1_3_3)))))\n"
    "(assert (= stmt_2_3_4 (ite stmt_1_3_3 (and exec_1_3_3 (not (not (= accu_1_3 #x0000)))) (and stmt_1_3_4 (not exec_1_3_4)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// void add_state_update (void);
TEST_F(SMTLibEncoderFunctionalTest, add_state_update)
{
  add_instruction_set(3);

  encoder->add_state_update();

  expected =
    "; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "(declare-fun accu_1_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_1_1 "
      "(ite exec_1_1_0 "
        "(select heap_0 #x0001) "
        "(ite exec_1_1_2 "
          "(bvadd accu_0_1 (select heap_0 #x0001)) "
          "(ite exec_1_1_3 "
            "(bvadd accu_0_1 #x0001) "
            "(ite exec_1_1_4 "
              "(bvsub accu_0_1 (select heap_0 #x0001)) "
              "(ite exec_1_1_5 "
                "(bvsub accu_0_1 #x0001) "
                "(ite exec_1_1_6 "
                  "(bvsub accu_0_1 (select heap_0 #x0001)) "
                  "(ite exec_1_1_13 "
                    "(select heap_0 #x0001) "
                    "(ite exec_1_1_14 "
                      "(ite (= mem_0_1 (select heap_0 #x0001)) #x0001 #x0000) "
                      "accu_0_1))))))))))\n"
    "(assert (= accu_1_2 "
      "(ite exec_1_2_0 "
        "(select heap_0 #x0001) "
        "(ite exec_1_2_2 "
          "(bvadd accu_0_2 (select heap_0 #x0001)) "
          "(ite exec_1_2_3 "
            "(bvadd accu_0_2 #x0001) "
            "(ite exec_1_2_4 "
              "(bvsub accu_0_2 (select heap_0 #x0001)) "
              "(ite exec_1_2_5 "
                "(bvsub accu_0_2 #x0001) "
                "(ite exec_1_2_6 "
                  "(bvsub accu_0_2 (select heap_0 #x0001)) "
                  "(ite exec_1_2_13 "
                    "(select heap_0 #x0001) "
                    "(ite exec_1_2_14 "
                      "(ite (= mem_0_2 (select heap_0 #x0001)) #x0001 #x0000) "
                      "accu_0_2))))))))))\n"
    "(assert (= accu_1_3 "
      "(ite exec_1_3_0 "
        "(select heap_0 #x0001) "
        "(ite exec_1_3_2 "
          "(bvadd accu_0_3 (select heap_0 #x0001)) "
          "(ite exec_1_3_3 "
            "(bvadd accu_0_3 #x0001) "
            "(ite exec_1_3_4 "
              "(bvsub accu_0_3 (select heap_0 #x0001)) "
              "(ite exec_1_3_5 "
                "(bvsub accu_0_3 #x0001) "
                "(ite exec_1_3_6 "
                  "(bvsub accu_0_3 (select heap_0 #x0001)) "
                  "(ite exec_1_3_13 "
                    "(select heap_0 #x0001) "
                    "(ite exec_1_3_14 "
                      "(ite (= mem_0_3 (select heap_0 #x0001)) #x0001 #x0000) "
                      "accu_0_3))))))))))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "(declare-fun mem_1_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_1_1 "
      "(ite exec_1_1_13 (select heap_0 #x0001) mem_0_1)))\n"
    "(assert (= mem_1_2 "
      "(ite exec_1_2_13 (select heap_0 #x0001) mem_0_2)))\n"
    "(assert (= mem_1_3 "
      "(ite exec_1_3_13 (select heap_0 #x0001) mem_0_3)))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_1 "
      "(ite exec_1_1_1 "
        "(store heap_0 #x0001 accu_0_1) "
        "(ite exec_1_1_14 "
          "(ite (= mem_0_1 (select heap_0 #x0001)) "
            "(store heap_0 #x0001 accu_0_1) "
            "heap_0) "
          "(ite exec_1_2_1 "
            "(store heap_0 #x0001 accu_0_2) "
            "(ite exec_1_2_14 "
              "(ite (= mem_0_2 (select heap_0 #x0001)) "
                "(store heap_0 #x0001 accu_0_2) "
                "heap_0) "
              "(ite exec_1_3_1 "
                "(store heap_0 #x0001 accu_0_3) "
                "(ite exec_1_3_14 "
                  "(ite (= mem_0_3 (select heap_0 #x0001)) "
                    "(store heap_0 #x0001 accu_0_3) "
                    "heap_0) "
                  "heap_0))))))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* no state altering statements */
  programs.clear();

  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("JMP", 1));
      programs[i]->push_back(Instruction::Set::create("JMP", 0));
    }

  reset_encoder(1, 1);

  encoder->add_state_update();

  expected =
    "; state update ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "(declare-fun accu_1_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_1_1 accu_0_1))\n"
    "(assert (= accu_1_2 accu_0_2))\n"
    "(assert (= accu_1_3 accu_0_3))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "(declare-fun mem_1_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_1_1 mem_0_1))\n"
    "(assert (= mem_1_2 mem_0_2))\n"
    "(assert (= mem_1_3 mem_0_3))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_1 heap_0))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(1, 1);

  verbose = false;
  encoder->add_state_update();
  verbose = true;

  expected =
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "(declare-fun accu_1_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_1_1 accu_0_1))\n"
    "(assert (= accu_1_2 accu_0_2))\n"
    "(assert (= accu_1_3 accu_0_3))\n"
    "\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "(declare-fun mem_1_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_1_1 mem_0_1))\n"
    "(assert (= mem_1_2 mem_0_2))\n"
    "(assert (= mem_1_3 mem_0_3))\n"
    "\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_1 heap_0))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// void add_exit_code (void);
TEST_F(SMTLibEncoderFunctionalTest, add_exit_code)
{
  /* no call to EXIT */
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", i));
    }

  encoder->add_exit_code();

  expected =
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit_code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit_code #x0000))\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* step 1 */
  programs.clear();

  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("EXIT", i));
    }

  reset_encoder(1, 1);

  encoder->add_exit_code();

  expected =
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit_code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit_code "
      "(ite exec_1_1_0 "
        "#x0000 "
        "(ite exec_1_2_0 "
          "#x0001 "
          "(ite exec_1_3_0 "
            "#x0002 "
            "#x0000)))))\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* reached bound */
  reset_encoder(3, 3);

  encoder->add_exit_code();

  expected =
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit_code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit_code "
      "(ite exec_1_1_0 "
        "#x0000 "
        "(ite exec_1_2_0 "
          "#x0001 "
          "(ite exec_1_3_0 "
            "#x0002 "
            "(ite exec_2_1_0 "
              "#x0000 "
              "(ite exec_2_2_0 "
                "#x0001 "
                "(ite exec_2_3_0 "
                  "#x0002 "
                  "(ite exec_3_1_0 "
                    "#x0000 "
                    "(ite exec_3_2_0 "
                      "#x0001 "
                      "(ite exec_3_3_0 "
                        "#x0002 "
                        "#x0000)))))))))))\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(3, 3);

  verbose = false;
  encoder->add_exit_code();
  verbose = true;

  expected =
    "(declare-fun exit_code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit_code "
      "(ite exec_1_1_0 "
        "#x0000 "
        "(ite exec_1_2_0 "
          "#x0001 "
          "(ite exec_1_3_0 "
            "#x0002 "
            "(ite exec_2_1_0 "
              "#x0000 "
              "(ite exec_2_2_0 "
                "#x0001 "
                "(ite exec_2_3_0 "
                  "#x0002 "
                  "(ite exec_3_1_0 "
                    "#x0000 "
                    "(ite exec_3_2_0 "
                      "#x0001 "
                      "(ite exec_3_3_0 "
                        "#x0002 "
                        "#x0000)))))))))))\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// virtual void encode (void);
TEST_F(SMTLibEncoderFunctionalTest, encode_sync)
{
  /* concurrent increment using SYNC */
  programs.push_back(
    create_from_file<Program>("data/increment.sync.thread.0.asm"));
  programs.push_back(
    create_from_file<Program>("data/increment.sync.thread.n.asm"));

  encoder =
    make_shared<SMTLibEncoderFunctional>(
      make_shared<ProgramList>(programs), 12);

  ifstream ifs("data/increment.sync.functional.t2.k12.smt2");
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, encode_cas)
{
  /* concurrent increment using CAS */
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));
  programs.push_back(create_from_file<Program>("data/increment.cas.asm"));

  encoder =
    make_shared<SMTLibEncoderFunctional>(
      make_shared<ProgramList>(programs), 12);

  ifstream ifs("data/increment.cas.functional.t2.k12.smt2");
  expected.assign(istreambuf_iterator<char>(ifs), istreambuf_iterator<char>());

  ASSERT_EQ(expected, encoder->formula.str());
}

// virtual std::string encode (Load &);
TEST_F(SMTLibEncoderFunctionalTest, LOAD)
{
  Load load = Load(1);

  ASSERT_EQ(
    "(select heap_0 #x0001)",
    encoder->encode(load));

  /* indirect */
  load.indirect = true;

  ASSERT_EQ(
    "(select heap_0 (select heap_0 #x0001))",
    encoder->encode(load));
}

// virtual std::string encode (Store &);
TEST_F(SMTLibEncoderFunctionalTest, STORE)
{
  Store store = Store(1);

  ASSERT_EQ(
    "(store heap_0 #x0001 accu_0_1)",
    encoder->encode(store));

  /* indirect */
  store.indirect = true;

  ASSERT_EQ(
    "(store heap_0 (select heap_0 #x0001) accu_0_1)",
    encoder->encode(store));
}

// virtual std::string encode (Add &);
TEST_F(SMTLibEncoderFunctionalTest, ADD)
{
  Add add = Add(1);

  ASSERT_EQ(
    "(bvadd accu_0_1 (select heap_0 #x0001))",
    encoder->encode(add));

  /* indirect */
  add.indirect = true;

  ASSERT_EQ(
    "(bvadd accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(add));
}

// virtual std::string encode (Addi &);
TEST_F(SMTLibEncoderFunctionalTest, ADDI)
{
  Addi addi = Addi(1);

  ASSERT_EQ(
    "(bvadd accu_0_1 #x0001)",
    encoder->encode(addi));
}

// virtual std::string encode (Sub &);
TEST_F(SMTLibEncoderFunctionalTest, SUB)
{
  Sub sub = Sub(1);

  ASSERT_EQ(
    "(bvsub accu_0_1 (select heap_0 #x0001))",
    encoder->encode(sub));

  /* indirect */
  sub.indirect = true;

  ASSERT_EQ(
    "(bvsub accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(sub));
}

// virtual std::string encode (Subi &);
TEST_F(SMTLibEncoderFunctionalTest, SUBI)
{
  Subi subi = Subi(1);

  ASSERT_EQ(
    "(bvsub accu_0_1 #x0001)",
    encoder->encode(subi));
}

// virtual std::string encode (Cmp &);
TEST_F(SMTLibEncoderFunctionalTest, CMP)
{
  Cmp cmp = Cmp(1);

  ASSERT_EQ(
    "(bvsub accu_0_1 (select heap_0 #x0001))",
    encoder->encode(cmp));

  /* indirect */
  cmp.indirect = true;

  ASSERT_EQ(
    "(bvsub accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(cmp));
}

// virtual std::string encode (Jmp &);
TEST_F(SMTLibEncoderFunctionalTest, JMP)
{
  Jmp jmp = Jmp(1);

  ASSERT_TRUE(encoder->encode(jmp).empty());
}

// virtual std::string encode (Jz &);
TEST_F(SMTLibEncoderFunctionalTest, JZ)
{
  Jz jz = Jz(1);

  ASSERT_EQ(
    "(= accu_0_1 #x0000)",
    encoder->encode(jz));
}

// virtual std::string encode (Jnz &);
TEST_F(SMTLibEncoderFunctionalTest, JNZ)
{
  Jnz jnz = Jnz(1);

  ASSERT_EQ(
    "(not (= accu_0_1 #x0000))",
    encoder->encode(jnz));
}

// virtual std::string encode (Js &);
TEST_F(SMTLibEncoderFunctionalTest, JS)
{
  Js js = Js(1);

  ASSERT_EQ(
    "(= #b1 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_0_1))",
    encoder->encode(js));
}

// virtual std::string encode (Jns &);
TEST_F(SMTLibEncoderFunctionalTest, JNS)
{
  Jns jns = Jns(1);

  ASSERT_EQ(
    "(= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_0_1))",
    encoder->encode(jns));
}

// virtual std::string encode (Jnzns &);
TEST_F(SMTLibEncoderFunctionalTest, JNZNS)
{
  Jnzns jnzns = Jnzns(1);

  ASSERT_EQ(
    "(and (not (= accu_0_1 #x0000)) (= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") accu_0_1)))",
    encoder->encode(jnzns));
}

// virtual std::string encode (Mem &);
TEST_F(SMTLibEncoderFunctionalTest, MEM)
{
  Mem mem = Mem(1);

  ASSERT_EQ(
    "(select heap_0 #x0001)",
    encoder->encode(mem));

  /* indirect */
  mem.indirect = true;

  ASSERT_EQ(
    "(select heap_0 (select heap_0 #x0001))",
    encoder->encode(mem));
}

// virtual std::string encode (Cas &);
TEST_F(SMTLibEncoderFunctionalTest, CAS)
{
  Cas cas = Cas(1);

  encoder->update_accu = true;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_1 (select heap_0 #x0001)) "
      "#x0001 "
      "#x0000)",
    encoder->encode(cas));

  encoder->update_accu = false;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_1 (select heap_0 #x0001)) "
      "(store heap_0 #x0001 accu_0_1) "
      "heap_0)",
    encoder->encode(cas));

  /* indirect */
  cas.indirect = true;

  encoder->update_accu = true;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_1 (select heap_0 (select heap_0 #x0001))) "
      "#x0001 "
      "#x0000)",
    encoder->encode(cas));

  encoder->update_accu = false;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_1 (select heap_0 (select heap_0 #x0001))) "
      "(store heap_0 (select heap_0 #x0001) accu_0_1) "
      "heap_0)",
    encoder->encode(cas));
}

// virtual std::string encode (Sync &);
TEST_F(SMTLibEncoderFunctionalTest, SYNC)
{
  Sync sync = Sync(1);

  ASSERT_TRUE(encoder->encode(sync).empty());
}

// virtual std::string encode (Exit &);
TEST_F(SMTLibEncoderFunctionalTest, EXIT)
{
  Exit exit = Exit(1);

  ASSERT_EQ("#x0001", encoder->encode(exit));
}
