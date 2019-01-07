#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct SMTLibEncoderFunctionalTest : public ::testing::Test
{
  const char *                expected;
  ProgramList                 programs;
  SMTLibEncoderFunctionalPtr  encoder = create_encoder(1, 1);

  SMTLibEncoderFunctionalPtr create_encoder (const word bound, const word step)
    {
      SMTLibEncoderFunctionalPtr e =
        make_shared<SMTLibEncoderFunctional>(
          make_shared<ProgramList>(programs),
          bound);

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

      reset_encoder(1, 1);
    }
};

// void add_statement_activation (void);
TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_basic)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
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

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JMP", 1));
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

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JZ", 1));
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
    "(assert (= stmt_2_1_1 (ite stmt_1_1_2 (and exec_1_1_2 (= accu_1_1 #x0000)) (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1))))))\n"
    "(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_2 (and exec_1_2_2 (= accu_1_2 #x0000)) (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1))))))\n"
    "(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (and stmt_1_3_0 (not exec_1_3_0))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_2 (and exec_1_3_2 (= accu_1_3 #x0000)) (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1))))))\n"
    "(assert (= stmt_2_3_2 (ite stmt_1_3_1 exec_1_3_1 (and stmt_1_3_2 (not exec_1_3_2)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_start)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JZ", 0));
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
    "(assert (= stmt_2_1_0 (ite stmt_1_1_2 (and exec_1_1_2 (= accu_1_1 #x0000)) (and stmt_1_1_0 (not exec_1_1_0)))))\n"
    "(assert (= stmt_2_1_1 (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1)))))\n"
    "(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (ite stmt_1_2_2 (and exec_1_2_2 (= accu_1_2 #x0000)) (and stmt_1_2_0 (not exec_1_2_0)))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1)))))\n"
    "(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (ite stmt_1_3_2 (and exec_1_3_2 (= accu_1_3 #x0000)) (and stmt_1_3_0 (not exec_1_3_0)))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1)))))\n"
    "(assert (= stmt_2_3_2 (ite stmt_1_3_1 exec_1_3_1 (and stmt_1_3_2 (not exec_1_3_2)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_statement_activation_jmp_twice)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
      programs[i]->add(Instruction::Set::create("STORE", 1));
      programs[i]->add(Instruction::Set::create("JZ", 1));
      programs[i]->add(Instruction::Set::create("JNZ", 1));
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
    "(assert (= stmt_2_1_1 (ite stmt_1_1_3 (and exec_1_1_3 (not (= accu_1_1 #x0000))) (ite stmt_1_1_2 (and exec_1_1_2 (= accu_1_1 #x0000)) (ite stmt_1_1_0 exec_1_1_0 (and stmt_1_1_1 (not exec_1_1_1)))))))\n"
    "(assert (= stmt_2_1_2 (ite stmt_1_1_1 exec_1_1_1 (and stmt_1_1_2 (not exec_1_1_2)))))\n"
    "(assert (= stmt_2_1_3 (ite stmt_1_1_2 (and exec_1_1_2 (not (= accu_1_1 #x0000))) (and stmt_1_1_3 (not exec_1_1_3)))))\n"
    "\n"
    "(assert (= stmt_2_2_0 (and stmt_1_2_0 (not exec_1_2_0))))\n"
    "(assert (= stmt_2_2_1 (ite stmt_1_2_3 (and exec_1_2_3 (not (= accu_1_2 #x0000))) (ite stmt_1_2_2 (and exec_1_2_2 (= accu_1_2 #x0000)) (ite stmt_1_2_0 exec_1_2_0 (and stmt_1_2_1 (not exec_1_2_1)))))))\n"
    "(assert (= stmt_2_2_2 (ite stmt_1_2_1 exec_1_2_1 (and stmt_1_2_2 (not exec_1_2_2)))))\n"
    "(assert (= stmt_2_2_3 (ite stmt_1_2_2 (and exec_1_2_2 (not (= accu_1_2 #x0000))) (and stmt_1_2_3 (not exec_1_2_3)))))\n"
    "\n"
    "(assert (= stmt_2_3_0 (and stmt_1_3_0 (not exec_1_3_0))))\n"
    "(assert (= stmt_2_3_1 (ite stmt_1_3_3 (and exec_1_3_3 (not (= accu_1_3 #x0000))) (ite stmt_1_3_2 (and exec_1_3_2 (= accu_1_3 #x0000)) (ite stmt_1_3_0 exec_1_3_0 (and stmt_1_3_1 (not exec_1_3_1)))))))\n"
    "(assert (= stmt_2_3_2 (ite stmt_1_3_1 exec_1_3_1 (and stmt_1_3_2 (not exec_1_3_2)))))\n"
    "(assert (= stmt_2_3_3 (ite stmt_1_3_2 (and exec_1_3_2 (not (= accu_1_3 #x0000))) (and stmt_1_3_3 (not exec_1_3_3)))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// void add_thread_scheduling (void);
TEST_F(SMTLibEncoderFunctionalTest, add_thread_scheduling_naive)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
    }

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  expected =
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n"
    "\n"
    "(assert (or thread_1_1 thread_1_2 thread_1_3))\n"
    "(assert (or (not thread_1_1) (not thread_1_2)))\n"
    "(assert (or (not thread_1_1) (not thread_1_3)))\n"
    "(assert (or (not thread_1_2) (not thread_1_3)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* EXIT call - step 1 */
  for (const auto & p : programs)
    p->add(Instruction::Set::create("EXIT", 1));

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  expected =
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n"
    "\n"
    "(assert (or thread_1_1 thread_1_2 thread_1_3))\n"
    "(assert (or (not thread_1_1) (not thread_1_2)))\n"
    "(assert (or (not thread_1_1) (not thread_1_3)))\n"
    "(assert (or (not thread_1_2) (not thread_1_3)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* EXIT call - step 2 */
  reset_encoder(2, 2);

  encoder->add_thread_scheduling();

  expected =
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n"
    "(declare-fun thread_2_3 () Bool)\n"
    "\n"
    "(assert (or thread_2_1 thread_2_2 thread_2_3 exit_2))\n"
    "(assert (or (not thread_2_1) (not thread_2_2)))\n"
    "(assert (or (not thread_2_1) (not thread_2_3)))\n"
    "(assert (or (not thread_2_1) (not exit_2)))\n"
    "(assert (or (not thread_2_2) (not thread_2_3)))\n"
    "(assert (or (not thread_2_2) (not exit_2)))\n"
    "(assert (or (not thread_2_3) (not exit_2)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(1, 1);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  expected =
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n"
    "\n"
    "(assert (or thread_1_1 thread_1_2 thread_1_3))\n"
    "(assert (or (not thread_1_1) (not thread_1_2)))\n"
    "(assert (or (not thread_1_1) (not thread_1_3)))\n"
    "(assert (or (not thread_1_2) (not thread_1_3)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

TEST_F(SMTLibEncoderFunctionalTest, add_thread_scheduling_sinz)
{
  for (size_t i = 0; i < 6; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("ADDI", 1));
    }

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  expected =
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n"
    "(declare-fun thread_1_4 () Bool)\n"
    "(declare-fun thread_1_5 () Bool)\n"
    "(declare-fun thread_1_6 () Bool)\n"
    "\n"
    "(declare-fun thread_1_1_aux () Bool)\n"
    "(declare-fun thread_1_2_aux () Bool)\n"
    "(declare-fun thread_1_3_aux () Bool)\n"
    "(declare-fun thread_1_4_aux () Bool)\n"
    "(declare-fun thread_1_5_aux () Bool)\n"
    "\n"
    "(assert (or thread_1_1 thread_1_2 thread_1_3 thread_1_4 thread_1_5 thread_1_6))\n"
    "(assert (or (not thread_1_1) thread_1_1_aux))\n"
    "(assert (or (not thread_1_6) (not thread_1_5_aux)))\n"
    "(assert (or (not thread_1_2) thread_1_2_aux))\n"
    "(assert (or (not thread_1_1_aux) thread_1_2_aux))\n"
    "(assert (or (not thread_1_2) (not thread_1_1_aux)))\n"
    "(assert (or (not thread_1_3) thread_1_3_aux))\n"
    "(assert (or (not thread_1_2_aux) thread_1_3_aux))\n"
    "(assert (or (not thread_1_3) (not thread_1_2_aux)))\n"
    "(assert (or (not thread_1_4) thread_1_4_aux))\n"
    "(assert (or (not thread_1_3_aux) thread_1_4_aux))\n"
    "(assert (or (not thread_1_4) (not thread_1_3_aux)))\n"
    "(assert (or (not thread_1_5) thread_1_5_aux))\n"
    "(assert (or (not thread_1_4_aux) thread_1_5_aux))\n"
    "(assert (or (not thread_1_5) (not thread_1_4_aux)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* EXIT call - step 1 */
  for (const auto & p : programs)
    p->add(Instruction::Set::create("EXIT", 1));

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  expected =
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n"
    "(declare-fun thread_1_4 () Bool)\n"
    "(declare-fun thread_1_5 () Bool)\n"
    "(declare-fun thread_1_6 () Bool)\n"
    "\n"
    "(declare-fun thread_1_1_aux () Bool)\n"
    "(declare-fun thread_1_2_aux () Bool)\n"
    "(declare-fun thread_1_3_aux () Bool)\n"
    "(declare-fun thread_1_4_aux () Bool)\n"
    "(declare-fun thread_1_5_aux () Bool)\n"
    "\n"
    "(assert (or thread_1_1 thread_1_2 thread_1_3 thread_1_4 thread_1_5 thread_1_6))\n"
    "(assert (or (not thread_1_1) thread_1_1_aux))\n"
    "(assert (or (not thread_1_6) (not thread_1_5_aux)))\n"
    "(assert (or (not thread_1_2) thread_1_2_aux))\n"
    "(assert (or (not thread_1_1_aux) thread_1_2_aux))\n"
    "(assert (or (not thread_1_2) (not thread_1_1_aux)))\n"
    "(assert (or (not thread_1_3) thread_1_3_aux))\n"
    "(assert (or (not thread_1_2_aux) thread_1_3_aux))\n"
    "(assert (or (not thread_1_3) (not thread_1_2_aux)))\n"
    "(assert (or (not thread_1_4) thread_1_4_aux))\n"
    "(assert (or (not thread_1_3_aux) thread_1_4_aux))\n"
    "(assert (or (not thread_1_4) (not thread_1_3_aux)))\n"
    "(assert (or (not thread_1_5) thread_1_5_aux))\n"
    "(assert (or (not thread_1_4_aux) thread_1_5_aux))\n"
    "(assert (or (not thread_1_5) (not thread_1_4_aux)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* EXIT call - step 2 */
  reset_encoder(2, 2);

  encoder->add_thread_scheduling();

  expected =
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n"
    "(declare-fun thread_2_3 () Bool)\n"
    "(declare-fun thread_2_4 () Bool)\n"
    "(declare-fun thread_2_5 () Bool)\n"
    "(declare-fun thread_2_6 () Bool)\n"
    "\n"
    "(declare-fun thread_2_1_aux () Bool)\n"
    "(declare-fun thread_2_2_aux () Bool)\n"
    "(declare-fun thread_2_3_aux () Bool)\n"
    "(declare-fun thread_2_4_aux () Bool)\n"
    "(declare-fun thread_2_5_aux () Bool)\n"
    "(declare-fun thread_2_6_aux () Bool)\n"
    "\n"
    "(assert (or thread_2_1 thread_2_2 thread_2_3 thread_2_4 thread_2_5 thread_2_6 exit_2))\n"
    "(assert (or (not thread_2_1) thread_2_1_aux))\n"
    "(assert (or (not exit_2) (not thread_2_6_aux)))\n"
    "(assert (or (not thread_2_2) thread_2_2_aux))\n"
    "(assert (or (not thread_2_1_aux) thread_2_2_aux))\n"
    "(assert (or (not thread_2_2) (not thread_2_1_aux)))\n"
    "(assert (or (not thread_2_3) thread_2_3_aux))\n"
    "(assert (or (not thread_2_2_aux) thread_2_3_aux))\n"
    "(assert (or (not thread_2_3) (not thread_2_2_aux)))\n"
    "(assert (or (not thread_2_4) thread_2_4_aux))\n"
    "(assert (or (not thread_2_3_aux) thread_2_4_aux))\n"
    "(assert (or (not thread_2_4) (not thread_2_3_aux)))\n"
    "(assert (or (not thread_2_5) thread_2_5_aux))\n"
    "(assert (or (not thread_2_4_aux) thread_2_5_aux))\n"
    "(assert (or (not thread_2_5) (not thread_2_4_aux)))\n"
    "(assert (or (not thread_2_6) thread_2_6_aux))\n"
    "(assert (or (not thread_2_5_aux) thread_2_6_aux))\n"
    "(assert (or (not thread_2_6) (not thread_2_5_aux)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// void add_exit_call (void);
TEST_F(SMTLibEncoderFunctionalTest, add_exit_call)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("EXIT", i));
    }

  /* step 1 */
  reset_encoder(10, 1);

  encoder->add_exit_call();

  ASSERT_EQ("", encoder->formula.str());

  /* step 2 */
  reset_encoder(10, 2);

  encoder->add_exit_call();

  expected =
    "; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit variable - exit_<step>\n"
    "(declare-fun exit_2 () Bool)\n"
    "\n"
    "(assert (= exit_2 (or exec_1_1_0 exec_1_2_0 exec_1_3_0)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* step 3 - reached bound */
  reset_encoder(3, 3);

  encoder->add_exit_call();

  expected =
    "; exit call ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit variable - exit_<step>\n"
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (= exit_3 (or exit_2 exec_2_1_0 exec_2_2_0 exec_2_3_0)))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* verbosity */
  reset_encoder(3, 3);

  verbose = false;
  encoder->add_exit_call();
  verbose = true;

  expected =
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (= exit_3 (or exit_2 exec_2_1_0 exec_2_2_0 exec_2_3_0)))\n\n";

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
    "(assert (= accu_1_1 \n"
      "(ite exec_1_1_0 "
        "(select heap_0 #x0001) \n"
        "(ite exec_1_1_2 "
          "(bvadd accu_0_1 (select heap_0 #x0001)) \n"
          "(ite exec_1_1_3 "
            "(bvadd accu_0_1 #x0001) \n"
            "(ite exec_1_1_4 "
              "(bvsub accu_0_1 (select heap_0 #x0001)) \n"
              "(ite exec_1_1_5 "
                "(bvsub accu_0_1 #x0001) \n"
                "(ite exec_1_1_6 "
                  "(bvsub accu_0_1 (select heap_0 #x0001)) "
                  "accu_0_1))))))))\n"
    "(assert (= accu_1_2 \n"
      "(ite exec_1_2_0 "
        "(select heap_0 #x0001) \n"
        "(ite exec_1_2_2 "
          "(bvadd accu_0_2 (select heap_0 #x0001)) \n"
          "(ite exec_1_2_3 "
            "(bvadd accu_0_2 #x0001) \n"
            "(ite exec_1_2_4 "
              "(bvsub accu_0_2 (select heap_0 #x0001)) \n"
              "(ite exec_1_2_5 "
                "(bvsub accu_0_2 #x0001) \n"
                "(ite exec_1_2_6 "
                  "(bvsub accu_0_2 (select heap_0 #x0001)) "
                  "accu_0_2))))))))\n"
    "(assert (= accu_1_3 \n"
      "(ite exec_1_3_0 "
        "(select heap_0 #x0001) \n"
        "(ite exec_1_3_2 "
          "(bvadd accu_0_3 (select heap_0 #x0001)) \n"
          "(ite exec_1_3_3 "
            "(bvadd accu_0_3 #x0001) \n"
            "(ite exec_1_3_4 "
              "(bvsub accu_0_3 (select heap_0 #x0001)) \n"
              "(ite exec_1_3_5 "
                "(bvsub accu_0_3 #x0001) \n"
                "(ite exec_1_3_6 "
                  "(bvsub accu_0_3 (select heap_0 #x0001)) "
                  "accu_0_3))))))))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "(declare-fun mem_1_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_1_1 \n"
      "(ite exec_1_1_13 (select heap_0 #x0001) mem_0_1)))\n"
    "(assert (= mem_1_2 \n"
      "(ite exec_1_2_13 (select heap_0 #x0001) mem_0_2)))\n"
    "(assert (= mem_1_3 \n"
      "(ite exec_1_3_13 (select heap_0 #x0001) mem_0_3)))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n"
    "(assert (= heap_1 \n"
      "(ite exec_1_1_1 "
        "(store heap_0 #x0001 accu_0_1) \n"
        "(ite exec_1_1_14 "
          "(ite (= mem_0_1 (select heap_0 #x0001)) "
            "(store heap_0 #x0001 accu_0_1) "
            "heap_0) \n"
          "(ite exec_1_2_1 "
            "(store heap_0 #x0001 accu_0_2) \n"
            "(ite exec_1_2_14 "
              "(ite (= mem_0_2 (select heap_0 #x0001)) "
                "(store heap_0 #x0001 accu_0_2) "
                "heap_0) \n"
              "(ite exec_1_3_1 "
                "(store heap_0 #x0001 accu_0_3) \n"
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

      programs[i]->add(Instruction::Set::create("JMP", 1));
      programs[i]->add(Instruction::Set::create("JMP", 0));
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
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->add(Instruction::Set::create("EXIT", i));
    }

  /* step 1 */
  reset_encoder(1, 1);

  encoder->add_exit_code();

  expected =
    "; exit code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(declare-fun exit_code () (_ BitVec 16))\n"
    "\n"
    "(assert (= exit_code #x0000))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());

  /* reached bound */
  reset_encoder(3, 3);

  encoder->add_exit_code();

  expected =
    "; exit code ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
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
                        "#x0000)))))))))))\n\n";

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
                        "#x0000)))))))))))\n\n";

  ASSERT_EQ(expected, encoder->formula.str());
}

// virtual void preprocess (void);
TEST_F(SMTLibEncoderFunctionalTest, preprocess)
{
  add_instruction_set(3);

  /* heap altering pcs */
  ASSERT_EQ(3, encoder->heap_pcs.size());

  vector<word> heap_pcs({1, 14});

  for (const auto & pcs: encoder->heap_pcs)
    ASSERT_EQ(heap_pcs, pcs.second);

  /* accu altering pcs */
  ASSERT_EQ(3, encoder->accu_pcs.size());

  vector<word> accu_pcs({0, 2, 3, 4, 5, 6});

  for (const auto & pcs: encoder->accu_pcs)
    ASSERT_EQ(accu_pcs, pcs.second);

  /* mem altering pcs */
  ASSERT_EQ(3, encoder->mem_pcs.size());

  vector<word> mem_pcs({13});

  for (const auto & pcs: encoder->mem_pcs)
    ASSERT_EQ(mem_pcs, pcs.second);
}

// virtual void encode (void);
// TODO
#include "boolector.hh"
TEST_F(SMTLibEncoderFunctionalTest, encode)
{
  programs.push_back(
    shared_ptr<Program>(
      new Program("../wiki/encoding/concurrent-increment.sync.thread1.asm")));
  programs.push_back(
    shared_ptr<Program>(
      new Program("../wiki/encoding/concurrent-increment.sync.thread2.asm")));

  encoder =
    make_shared<SMTLibEncoderFunctional>(
      make_shared<ProgramList>(programs), 20);

  encoder->encode();

  Boolector btor;

  string formula = encoder->to_string();

  btor.sat(formula);

  cout << btor.std_out << eol;

  ASSERT_EQ("", formula);
}

// virtual std::string encode (Load &);
TEST_F(SMTLibEncoderFunctionalTest, LOAD)
{
  Load load = Load(1);

  ASSERT_STREQ(
    "(select heap_0 #x0001)",
    encoder->encode(load).c_str());

  /* indirect */
  load.indirect = true;

  ASSERT_STREQ(
    "(select heap_0 (select heap_0 #x0001))",
    encoder->encode(load).c_str());
}

// virtual std::string encode (Store &);
TEST_F(SMTLibEncoderFunctionalTest, STORE)
{
  Store store = Store(1);

  ASSERT_STREQ(
    "(store heap_0 #x0001 accu_0_1)",
    encoder->encode(store).c_str());

  /* indirect */
  store.indirect = true;

  ASSERT_STREQ(
    "(store heap_0 (select heap_0 #x0001) accu_0_1)",
    encoder->encode(store).c_str());
}

// virtual std::string encode (Add &);
TEST_F(SMTLibEncoderFunctionalTest, ADD)
{
  Add add = Add(1);

  ASSERT_STREQ(
    "(bvadd accu_0_1 (select heap_0 #x0001))",
    encoder->encode(add).c_str());

  /* indirect */
  add.indirect = true;

  ASSERT_STREQ(
    "(bvadd accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(add).c_str());
}

// virtual std::string encode (Addi &);
TEST_F(SMTLibEncoderFunctionalTest, ADDI)
{
  Addi addi = Addi(1);

  ASSERT_STREQ(
    "(bvadd accu_0_1 #x0001)",
    encoder->encode(addi).c_str());
}

// virtual std::string encode (Sub &);
TEST_F(SMTLibEncoderFunctionalTest, SUB)
{
  Sub sub = Sub(1);

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 #x0001))",
    encoder->encode(sub).c_str());

  /* indirect */
  sub.indirect = true;

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(sub).c_str());
}

// virtual std::string encode (Subi &);
TEST_F(SMTLibEncoderFunctionalTest, SUBI)
{
  Subi subi = Subi(1);

  ASSERT_STREQ(
    "(bvsub accu_0_1 #x0001)",
    encoder->encode(subi).c_str());
}

// virtual std::string encode (Cmp &);
TEST_F(SMTLibEncoderFunctionalTest, CMP)
{
  Cmp cmp = Cmp(1);

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 #x0001))",
    encoder->encode(cmp).c_str());

  /* indirect */
  cmp.indirect = true;

  ASSERT_STREQ(
    "(bvsub accu_0_1 (select heap_0 (select heap_0 #x0001)))",
    encoder->encode(cmp).c_str());
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

  ASSERT_STREQ(
    "(= accu_0_1 #x0000)",
    encoder->encode(jz).c_str());
}

// virtual std::string encode (Jnz &);
TEST_F(SMTLibEncoderFunctionalTest, JNZ)
{
  Jnz jnz = Jnz(1);

  ASSERT_STREQ(
    "(not (= accu_0_1 #x0000))",
    encoder->encode(jnz).c_str());
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

  ASSERT_STREQ(
    "(select heap_0 #x0001)",
    encoder->encode(mem).c_str());

  /* indirect */
  mem.indirect = true;

  ASSERT_STREQ(
    "(select heap_0 (select heap_0 #x0001))",
    encoder->encode(mem).c_str());
}

// virtual std::string encode (Cas &);
TEST_F(SMTLibEncoderFunctionalTest, CAS)
{
  Cas cas = Cas(1);

  ASSERT_STREQ(
    "(ite "
      "(= mem_0_1 (select heap_0 #x0001)) "
      "(store heap_0 #x0001 accu_0_1) "
      "heap_0)",
    encoder->encode(cas).c_str());

  /* indirect */
  cas.indirect = true;

  ASSERT_STREQ(
    "(ite "
      "(= mem_0_1 (select heap_0 (select heap_0 #x0001))) "
      "(store heap_0 (select heap_0 #x0001) accu_0_1) "
      "heap_0)",
    encoder->encode(cas).c_str());
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

  ASSERT_STREQ("#x0001", encoder->encode(exit).c_str());
}

/*******************************************************************************
 * DEPRECATED
*******************************************************************************/
#ifdef __NIGNORE__
TEST_F(EncoderTest, test)
{
  const char * program1 = "../wiki/encoding/concurrent-increment.sync.thread1.asm";
  const char * program2 = "../wiki/encoding/concurrent-increment.sync.thread2.asm";

  programs.push_back(make_shared<Program>(program1));
  programs.push_back(make_shared<Program>(program2));

  encoder = make_shared<SMTLibEncoderFunctional>(make_shared<ProgramList>(programs), 3);

  encoder->encode();

  string formula = encoder->to_string();

  ASSERT_STREQ("", formula.c_str());
}
#endif
