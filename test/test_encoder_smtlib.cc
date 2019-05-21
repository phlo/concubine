#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct SMTLibEncoderTest : public ::testing::Test
{
  ProgramList       programs;
  SMTLibEncoderPtr  encoder = create_encoder(0);

  SMTLibEncoderPtr create_encoder (const word bound)
    {
      return make_shared<SMTLibEncoderFunctional>(
        make_shared<ProgramList>(programs),
        bound,
        false);
    }

  void reset_encoder (const word bound, unsigned long step)
    {
      encoder = create_encoder(bound);
      encoder->step = step;
    }

  void add_dummy_programs (unsigned num, unsigned size)
    {
      Instruction_ptr op = Instruction::Set::create("ADDI", 1);
      for (size_t i = 0; i < num; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));
          for (size_t j = 0; j < size; j++)
            programs[i]->push_back(op);
        }

      encoder = create_encoder(0);
    }
};

// string heap_var (const word);
TEST_F(SMTLibEncoderTest, heap_var_args)
{
  ASSERT_EQ("heap_0", encoder->heap_var(0));
  ASSERT_EQ("heap_1", encoder->heap_var(1));
  ASSERT_EQ("heap_2", encoder->heap_var(2));
}

// string heap_var (void);
TEST_F(SMTLibEncoderTest, heap_var)
{
  ASSERT_EQ("heap_0", encoder->heap_var());

  encoder->step = 1;
  ASSERT_EQ("heap_1", encoder->heap_var());

  encoder->step = 2;
  ASSERT_EQ("heap_2", encoder->heap_var());
}

// string accu_var (const word, const word);
TEST_F(SMTLibEncoderTest, accu_var_args)
{
  ASSERT_EQ("accu_0_1", encoder->accu_var(0, 1));
  ASSERT_EQ("accu_1_2", encoder->accu_var(1, 2));
  ASSERT_EQ("accu_2_3", encoder->accu_var(2, 3));
}

// string accu_var (void);
TEST_F(SMTLibEncoderTest, accu_var)
{
  encoder->thread = 1;
  ASSERT_EQ("accu_0_1", encoder->accu_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("accu_1_2", encoder->accu_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("accu_2_3", encoder->accu_var());
}

// string mem_var (const word, const word);
TEST_F(SMTLibEncoderTest, mem_var_args)
{
  ASSERT_EQ("mem_0_1", encoder->mem_var(0, 1));
  ASSERT_EQ("mem_1_2", encoder->mem_var(1, 2));
  ASSERT_EQ("mem_2_3", encoder->mem_var(2, 3));
}

// string mem_var (void);
TEST_F(SMTLibEncoderTest, mem_var)
{
  encoder->thread = 1;
  ASSERT_EQ("mem_0_1", encoder->mem_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("mem_1_2", encoder->mem_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("mem_2_3", encoder->mem_var());
}

// string stmt_var (const word, const word, const word);
TEST_F(SMTLibEncoderTest, stmt_var_args)
{
  ASSERT_EQ("stmt_0_1_2", encoder->stmt_var(0, 1, 2));
  ASSERT_EQ("stmt_1_2_3", encoder->stmt_var(1, 2, 3));
  ASSERT_EQ("stmt_2_3_4", encoder->stmt_var(2, 3, 4));
}

// string stmt_var (void);
TEST_F(SMTLibEncoderTest, stmt_var)
{
  encoder->thread = 1;
  encoder->pc = 2;
  ASSERT_EQ("stmt_0_1_2", encoder->stmt_var());

  encoder->step = 1;
  encoder->thread = 2;
  encoder->pc = 3;
  ASSERT_EQ("stmt_1_2_3", encoder->stmt_var());

  encoder->step = 2;
  encoder->thread = 3;
  encoder->pc = 4;
  ASSERT_EQ("stmt_2_3_4", encoder->stmt_var());
}

// string thread_var (const word, const word);
TEST_F(SMTLibEncoderTest, thread_var_args)
{
  ASSERT_EQ("thread_0_1", encoder->thread_var(0, 1));
  ASSERT_EQ("thread_1_2", encoder->thread_var(1, 2));
  ASSERT_EQ("thread_2_3", encoder->thread_var(2, 3));
}

// string thread_var (void);
TEST_F(SMTLibEncoderTest, thread_var)
{
  encoder->thread = 1;
  ASSERT_EQ("thread_0_1", encoder->thread_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("thread_1_2", encoder->thread_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("thread_2_3", encoder->thread_var());
}

// string exec_var (const word, const word, const word);
TEST_F(SMTLibEncoderTest, exec_var_args)
{
  ASSERT_EQ("exec_0_1_2", encoder->exec_var(0, 1, 2));
  ASSERT_EQ("exec_1_2_3", encoder->exec_var(1, 2, 3));
  ASSERT_EQ("exec_2_3_4", encoder->exec_var(2, 3, 4));
}

// string exec_var (void);
TEST_F(SMTLibEncoderTest, exec_var)
{
  encoder->thread = 1;
  encoder->pc = 2;
  ASSERT_EQ("exec_0_1_2", encoder->exec_var());

  encoder->step = 1;
  encoder->thread = 2;
  encoder->pc = 3;
  ASSERT_EQ("exec_1_2_3", encoder->exec_var());

  encoder->step = 2;
  encoder->thread = 3;
  encoder->pc = 4;
  ASSERT_EQ("exec_2_3_4", encoder->exec_var());
}

// string cas_var (const word, const word);
TEST_F(SMTLibEncoderTest, cas_var_args)
{
  ASSERT_EQ("cas_0_1", encoder->cas_var(0, 1));
  ASSERT_EQ("cas_1_2", encoder->cas_var(1, 2));
  ASSERT_EQ("cas_2_3", encoder->cas_var(2, 3));
}

// string cas_var (void);
TEST_F(SMTLibEncoderTest, cas_var)
{
  encoder->thread = 1;
  ASSERT_EQ("cas_0_1", encoder->cas_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("cas_1_2", encoder->cas_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("cas_2_3", encoder->cas_var());
}

// std::string block_var (const word, const word, const word);
TEST_F(SMTLibEncoderTest, block_var_args)
{
  ASSERT_EQ("block_6_3_0", encoder->block_var(6, 3, 0));
  ASSERT_EQ("block_7_4_1", encoder->block_var(7, 4, 1));
  ASSERT_EQ("block_8_5_2", encoder->block_var(8, 5, 2));
}

// string check_var (const word, const word);
TEST_F(SMTLibEncoderTest, check_var_args)
{
  ASSERT_EQ("check_0_1", encoder->check_var(0, 1));
  ASSERT_EQ("check_1_2", encoder->check_var(1, 2));
  ASSERT_EQ("check_2_3", encoder->check_var(2, 3));
}

// string exit_var (const word);
TEST_F(SMTLibEncoderTest, exit_var_args)
{
  ASSERT_EQ("exit_0", encoder->exit_var(0));
  ASSERT_EQ("exit_1", encoder->exit_var(1));
  ASSERT_EQ("exit_2", encoder->exit_var(2));
}

// string exit_var (void);
TEST_F(SMTLibEncoderTest, exit_var)
{
  encoder->thread = 1;
  ASSERT_EQ("exit_0", encoder->exit_var());

  encoder->step = 1;
  ASSERT_EQ("exit_1", encoder->exit_var());

  encoder->step = 2;
  ASSERT_EQ("exit_2", encoder->exit_var());
}

// void declare_heap_var (void);
TEST_F(SMTLibEncoderTest, declare_heap_var)
{
  encoder->declare_heap_var();

  ASSERT_EQ(
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder->formula.str());
}

// void declare_accu_vars (void);
TEST_F(SMTLibEncoderTest, declare_accu_vars)
{
  add_dummy_programs(3, 3);

  /* step 0 */
  encoder->declare_accu_vars();

  ASSERT_EQ(
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n\n",
    encoder->formula.str());

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_accu_vars();

  ASSERT_EQ(
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_accu_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n\n",
    encoder->formula.str());
}

// void declare_mem_vars (void);
TEST_F(SMTLibEncoderTest, declare_mem_vars)
{
  add_dummy_programs(3, 3);

  /* step 0 */
  encoder->declare_mem_vars();

  ASSERT_EQ(
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n\n",
    encoder->formula.str());

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_mem_vars();

  ASSERT_EQ(
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_mem_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n\n",
    encoder->formula.str());
}

// void declare_stmt_vars (void);
TEST_F(SMTLibEncoderTest, declare_stmt_vars)
{
  add_dummy_programs(3, 3);

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_stmt_vars();

  ASSERT_EQ(
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
    "(declare-fun stmt_1_2_2 () Bool)\n\n",
    encoder->formula.str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_stmt_vars();

  ASSERT_EQ(
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

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_stmt_vars();
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
    "(declare-fun stmt_1_2_2 () Bool)\n\n",
    encoder->formula.str());
}

// void declare_thread_vars (void);
TEST_F(SMTLibEncoderTest, declare_thread_vars)
{
  add_dummy_programs(3, 3);

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_thread_vars();

  ASSERT_EQ(
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n",
    encoder->formula.str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_thread_vars();

  ASSERT_EQ(
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_thread_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n",
    encoder->formula.str());
}

// void declare_exec_vars (void);
TEST_F(SMTLibEncoderTest, declare_exec_vars)
{
  add_dummy_programs(3, 3);

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_exec_vars();

  ASSERT_EQ(
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_1_0_0 () Bool)\n"
    "(declare-fun exec_1_0_1 () Bool)\n"
    "(declare-fun exec_1_0_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_1_0 () Bool)\n"
    "(declare-fun exec_1_1_1 () Bool)\n"
    "(declare-fun exec_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "(declare-fun exec_1_2_1 () Bool)\n"
    "(declare-fun exec_1_2_2 () Bool)\n\n",
    encoder->formula.str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_exec_vars();

  ASSERT_EQ(
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_2_0_0 () Bool)\n"
    "(declare-fun exec_2_0_1 () Bool)\n"
    "(declare-fun exec_2_0_2 () Bool)\n"
    "\n"
    "(declare-fun exec_2_1_0 () Bool)\n"
    "(declare-fun exec_2_1_1 () Bool)\n"
    "(declare-fun exec_2_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_2_2_0 () Bool)\n"
    "(declare-fun exec_2_2_1 () Bool)\n"
    "(declare-fun exec_2_2_2 () Bool)\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_exec_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun exec_1_0_0 () Bool)\n"
    "(declare-fun exec_1_0_1 () Bool)\n"
    "(declare-fun exec_1_0_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_1_0 () Bool)\n"
    "(declare-fun exec_1_1_1 () Bool)\n"
    "(declare-fun exec_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "(declare-fun exec_1_2_1 () Bool)\n"
    "(declare-fun exec_1_2_2 () Bool)\n\n",
    encoder->formula.str());
}

// void declare_cas_vars (void);
TEST_F(SMTLibEncoderTest, declare_cas_vars)
{
  add_dummy_programs(3, 3);

  /* no CAS statement */
  encoder->declare_cas_vars();

  ASSERT_EQ("", encoder->formula.str());

  /* single CAS in thread 1 */
  programs[0]->push_back(Instruction::Set::create("CAS", 0));

  reset_encoder(0, 1);

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_0 () Bool)\n\n",
    encoder->formula.str());

  /* 1 CAS per thread */
  for (const auto & p : programs)
      p->push_back(Instruction::Set::create("CAS", 0));

  reset_encoder(0, 1);

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_0 () Bool)\n"
    "(declare-fun cas_1_1 () Bool)\n"
    "(declare-fun cas_1_2 () Bool)\n\n",
    encoder->formula.str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_2_0 () Bool)\n"
    "(declare-fun cas_2_1 () Bool)\n"
    "(declare-fun cas_2_2 () Bool)\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_cas_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun cas_1_0 () Bool)\n"
    "(declare-fun cas_1_1 () Bool)\n"
    "(declare-fun cas_1_2 () Bool)\n\n",
    encoder->formula.str());
}

// void declare_block_vars (void);
TEST_F(SMTLibEncoderTest, declare_block_vars)
{
  add_dummy_programs(3, 3);

  /* single checkpoint id */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("CHECK", 0));

  reset_encoder(0, 2);

  encoder->declare_block_vars();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_2_0_0 () Bool)\n"
    "(declare-fun block_2_0_1 () Bool)\n"
    "(declare-fun block_2_0_2 () Bool)\n\n",
    encoder->formula.str());

  /* two checkpoint ids */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("CHECK", 1));

  reset_encoder(0, 2);

  encoder->declare_block_vars();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_2_0_0 () Bool)\n"
    "(declare-fun block_2_0_1 () Bool)\n"
    "(declare-fun block_2_0_2 () Bool)\n"
    "(declare-fun block_2_1_0 () Bool)\n"
    "(declare-fun block_2_1_1 () Bool)\n"
    "(declare-fun block_2_1_2 () Bool)\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 2);

  verbose = false;
  encoder->declare_block_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun block_2_0_0 () Bool)\n"
    "(declare-fun block_2_0_1 () Bool)\n"
    "(declare-fun block_2_0_2 () Bool)\n"
    "(declare-fun block_2_1_0 () Bool)\n"
    "(declare-fun block_2_1_1 () Bool)\n"
    "(declare-fun block_2_1_2 () Bool)\n\n",
    encoder->formula.str());
}

// void declare_check_vars (void);
TEST_F(SMTLibEncoderTest, declare_check_vars)
{
  add_dummy_programs(3, 3);

  word check_id = 1;

  /* 3 different checkpoint ids */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("CHECK", check_id++));

  reset_encoder(0, 1);

  encoder->declare_check_vars();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n\n",
    encoder->formula.str());

  /* same checkpoint ids */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("CHECK", check_id));

  reset_encoder(0, 1);

  encoder->declare_check_vars();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n\n",
    encoder->formula.str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_check_vars();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_2_1 () Bool)\n"
    "(declare-fun check_2_2 () Bool)\n"
    "(declare-fun check_2_3 () Bool)\n"
    "(declare-fun check_2_4 () Bool)\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_check_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n\n",
    encoder->formula.str());
}

// void declare_exit_var (void);
TEST_F(SMTLibEncoderTest, declare_exit_vars)
{
  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_exit_var();

  ASSERT_EQ(
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_1 () Bool)\n\n",
    encoder->formula.str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_exit_var();

  ASSERT_EQ(
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_2 () Bool)\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_exit_var();
  verbose = true;

  ASSERT_EQ("(declare-fun exit_1 () Bool)\n\n", encoder->formula.str());
}

// void declare_exit_code (void);
TEST_F(SMTLibEncoderTest, declare_exit_code)
{
  encoder->declare_exit_code();

  ASSERT_EQ(
    "(declare-fun exit-code () (_ BitVec 16))\n\n",
    encoder->formula.str());
}

// string assign_var (string, string);
TEST_F(SMTLibEncoderTest, assign_var)
{
  ASSERT_EQ("(assert (= foo bar))", encoder->assign_var("foo", "bar"));
}

// void add_initial_state (void);
TEST_F(SMTLibEncoderTest, add_initial_state)
{
  add_dummy_programs(3, 3);

  encoder->add_initial_state();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; initial state\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 0);

  verbose = false;
  encoder->add_initial_state();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n"
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder->formula.str());
}

// void add_initial_statement_activation (void);
TEST_F(SMTLibEncoderTest, add_initial_statement_activation)
{
  add_dummy_programs(3, 3);

  encoder->step = 1;

  encoder->add_initial_statement_activation();

  ASSERT_EQ(
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

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->add_initial_statement_activation();
  verbose = true;

  ASSERT_EQ(
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

// void add_exit_flag (void);
TEST_F(SMTLibEncoderTest, add_exit_flag)
{
  /* no call to EXIT in step 2 */
  add_dummy_programs(3, 2);

  encoder->add_exit_flag();

  ASSERT_EQ("", encoder->formula.str());

  /* step 1 */
  programs.clear();

  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("EXIT", i));
    }

  reset_encoder(10, 1);

  encoder->add_exit_flag();

  ASSERT_EQ("", encoder->formula.str());

  /* step 2 */
  reset_encoder(10, 2);

  encoder->add_exit_flag();

  ASSERT_EQ(
    "; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_2 () Bool)\n"
    "\n"
    "(assert (= exit_2 (or exec_1_0_0 exec_1_1_0 exec_1_2_0)))\n\n",
    encoder->formula.str());

  /* step 3 - reached bound */
  reset_encoder(3, 3);

  encoder->add_exit_flag();

  ASSERT_EQ(
    "; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (= exit_3 (or exit_2 exec_2_0_0 exec_2_1_0 exec_2_2_0)))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(3, 3);

  verbose = false;
  encoder->add_exit_flag();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (= exit_3 (or exit_2 exec_2_0_0 exec_2_1_0 exec_2_2_0)))\n\n",
    encoder->formula.str());
}

// void add_thread_scheduling (void);
TEST_F(SMTLibEncoderTest, add_thread_scheduling_naive)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
    }

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n"
    "(assert (or thread_1_0 thread_1_1 thread_1_2))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not thread_1_2)))\n"
    "(assert (or (not thread_1_1) (not thread_1_2)))\n\n",
    encoder->formula.str());

  /* EXIT call - step 1 */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("EXIT", 1));

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n"
    "(assert (or thread_1_0 thread_1_1 thread_1_2))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not thread_1_2)))\n"
    "(assert (or (not thread_1_1) (not thread_1_2)))\n\n",
    encoder->formula.str());

  /* EXIT call - step 2 */
  reset_encoder(2, 2);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n"
    "\n"
    "(assert (or thread_2_0 thread_2_1 thread_2_2 exit_2))\n"
    "(assert (or (not thread_2_0) (not thread_2_1)))\n"
    "(assert (or (not thread_2_0) (not thread_2_2)))\n"
    "(assert (or (not thread_2_0) (not exit_2)))\n"
    "(assert (or (not thread_2_1) (not thread_2_2)))\n"
    "(assert (or (not thread_2_1) (not exit_2)))\n"
    "(assert (or (not thread_2_2) (not exit_2)))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1, 1);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n"
    "(assert (or thread_1_0 thread_1_1 thread_1_2))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not thread_1_2)))\n"
    "(assert (or (not thread_1_1) (not thread_1_2)))\n\n",
    encoder->formula.str());
}

TEST_F(SMTLibEncoderTest, add_thread_scheduling_sinz)
{
  for (size_t i = 0; i < 6; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
    }

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n"
    "(declare-fun thread_1_4 () Bool)\n"
    "(declare-fun thread_1_5 () Bool)\n"
    "\n"
    "(declare-fun thread_1_0_aux () Bool)\n"
    "(declare-fun thread_1_1_aux () Bool)\n"
    "(declare-fun thread_1_2_aux () Bool)\n"
    "(declare-fun thread_1_3_aux () Bool)\n"
    "(declare-fun thread_1_4_aux () Bool)\n"
    "\n"
    "(assert (or thread_1_0 thread_1_1 thread_1_2 thread_1_3 thread_1_4 thread_1_5))\n"
    "(assert (or (not thread_1_0) thread_1_0_aux))\n"
    "(assert (or (not thread_1_5) (not thread_1_4_aux)))\n"
    "(assert (or (not thread_1_1) thread_1_1_aux))\n"
    "(assert (or (not thread_1_0_aux) thread_1_1_aux))\n"
    "(assert (or (not thread_1_1) (not thread_1_0_aux)))\n"
    "(assert (or (not thread_1_2) thread_1_2_aux))\n"
    "(assert (or (not thread_1_1_aux) thread_1_2_aux))\n"
    "(assert (or (not thread_1_2) (not thread_1_1_aux)))\n"
    "(assert (or (not thread_1_3) thread_1_3_aux))\n"
    "(assert (or (not thread_1_2_aux) thread_1_3_aux))\n"
    "(assert (or (not thread_1_3) (not thread_1_2_aux)))\n"
    "(assert (or (not thread_1_4) thread_1_4_aux))\n"
    "(assert (or (not thread_1_3_aux) thread_1_4_aux))\n"
    "(assert (or (not thread_1_4) (not thread_1_3_aux)))\n\n",
    encoder->formula.str());

  /* EXIT call - step 1 */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("EXIT", 1));

  reset_encoder(1, 1);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n"
    "(declare-fun thread_1_4 () Bool)\n"
    "(declare-fun thread_1_5 () Bool)\n"
    "\n"
    "(declare-fun thread_1_0_aux () Bool)\n"
    "(declare-fun thread_1_1_aux () Bool)\n"
    "(declare-fun thread_1_2_aux () Bool)\n"
    "(declare-fun thread_1_3_aux () Bool)\n"
    "(declare-fun thread_1_4_aux () Bool)\n"
    "\n"
    "(assert (or thread_1_0 thread_1_1 thread_1_2 thread_1_3 thread_1_4 thread_1_5))\n"
    "(assert (or (not thread_1_0) thread_1_0_aux))\n"
    "(assert (or (not thread_1_5) (not thread_1_4_aux)))\n"
    "(assert (or (not thread_1_1) thread_1_1_aux))\n"
    "(assert (or (not thread_1_0_aux) thread_1_1_aux))\n"
    "(assert (or (not thread_1_1) (not thread_1_0_aux)))\n"
    "(assert (or (not thread_1_2) thread_1_2_aux))\n"
    "(assert (or (not thread_1_1_aux) thread_1_2_aux))\n"
    "(assert (or (not thread_1_2) (not thread_1_1_aux)))\n"
    "(assert (or (not thread_1_3) thread_1_3_aux))\n"
    "(assert (or (not thread_1_2_aux) thread_1_3_aux))\n"
    "(assert (or (not thread_1_3) (not thread_1_2_aux)))\n"
    "(assert (or (not thread_1_4) thread_1_4_aux))\n"
    "(assert (or (not thread_1_3_aux) thread_1_4_aux))\n"
    "(assert (or (not thread_1_4) (not thread_1_3_aux)))\n\n",
    encoder->formula.str());

  /* EXIT call - step 2 */
  reset_encoder(2, 2);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n"
    "(declare-fun thread_2_3 () Bool)\n"
    "(declare-fun thread_2_4 () Bool)\n"
    "(declare-fun thread_2_5 () Bool)\n"
    "\n"
    "(declare-fun thread_2_0_aux () Bool)\n"
    "(declare-fun thread_2_1_aux () Bool)\n"
    "(declare-fun thread_2_2_aux () Bool)\n"
    "(declare-fun thread_2_3_aux () Bool)\n"
    "(declare-fun thread_2_4_aux () Bool)\n"
    "(declare-fun thread_2_5_aux () Bool)\n"
    "\n"
    "(assert (or thread_2_0 thread_2_1 thread_2_2 thread_2_3 thread_2_4 thread_2_5 exit_2))\n"
    "(assert (or (not thread_2_0) thread_2_0_aux))\n"
    "(assert (or (not exit_2) (not thread_2_5_aux)))\n"
    "(assert (or (not thread_2_1) thread_2_1_aux))\n"
    "(assert (or (not thread_2_0_aux) thread_2_1_aux))\n"
    "(assert (or (not thread_2_1) (not thread_2_0_aux)))\n"
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
    "(assert (or (not thread_2_5) (not thread_2_4_aux)))\n\n",
    encoder->formula.str());
}

// void add_checkpoint_constraints (void);
TEST_F(SMTLibEncoderTest, add_checkpoint_constraints)
{
  /* single checkpoint - step 2 */
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));
      programs[i]->push_back(Instruction::Set::create("CHECK", 1));
    }

  reset_encoder(0, 2);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_2_1_0 () Bool)\n"
    "(declare-fun block_2_1_1 () Bool)\n"
    "(declare-fun block_2_1_2 () Bool)\n"
    "\n"
    "(assert (= block_2_1_0 exec_1_0_0))\n"
    "(assert (= block_2_1_1 exec_1_1_0))\n"
    "(assert (= block_2_1_2 exec_1_2_0))\n"
    "\n"
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_2_1 () Bool)\n"
    "\n"
    "(assert (= check_2_1 (and block_2_1_0 block_2_1_1 block_2_1_2)))\n"
    "\n"
    "; prevent scheduling of waiting threads\n"
    "(assert (=> (and block_2_1_0 (not check_2_1)) (not thread_2_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_2_1_1 (not check_2_1)) (not thread_2_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_2_1_2 (not check_2_1)) (not thread_2_2))) ; checkpoint 1: thread 2\n\n",
    encoder->formula.str());

  /* single checkpoint - step 3+ */
  reset_encoder(0, 3);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_3_1_0 () Bool)\n"
    "(declare-fun block_3_1_1 () Bool)\n"
    "(declare-fun block_3_1_2 () Bool)\n"
    "\n"
    "(assert (= block_3_1_0 (ite check_2_1 false (or exec_2_0_0 block_2_1_0))))\n"
    "(assert (= block_3_1_1 (ite check_2_1 false (or exec_2_1_0 block_2_1_1))))\n"
    "(assert (= block_3_1_2 (ite check_2_1 false (or exec_2_2_0 block_2_1_2))))\n"
    "\n"
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_3_1 () Bool)\n"
    "\n"
    "(assert (= check_3_1 (and block_3_1_0 block_3_1_1 block_3_1_2)))\n"
    "\n"
    "; prevent scheduling of waiting threads\n"
    "(assert (=> (and block_3_1_0 (not check_3_1)) (not thread_3_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_3_1_1 (not check_3_1)) (not thread_3_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_3_1_2 (not check_3_1)) (not thread_3_2))) ; checkpoint 1: thread 2\n\n",
    encoder->formula.str());

  /* two different checkpoints */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("CHECK", 2));

  reset_encoder(0, 3);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_3_1_0 () Bool)\n"
    "(declare-fun block_3_1_1 () Bool)\n"
    "(declare-fun block_3_1_2 () Bool)\n"
    "(declare-fun block_3_2_0 () Bool)\n"
    "(declare-fun block_3_2_1 () Bool)\n"
    "(declare-fun block_3_2_2 () Bool)\n"
    "\n"
    "(assert (= block_3_1_0 (ite check_2_1 false (or exec_2_0_0 block_2_1_0))))\n"
    "(assert (= block_3_1_1 (ite check_2_1 false (or exec_2_1_0 block_2_1_1))))\n"
    "(assert (= block_3_1_2 (ite check_2_1 false (or exec_2_2_0 block_2_1_2))))\n"
    "(assert (= block_3_2_0 (ite check_2_2 false (or exec_2_0_1 block_2_2_0))))\n"
    "(assert (= block_3_2_1 (ite check_2_2 false (or exec_2_1_1 block_2_2_1))))\n"
    "(assert (= block_3_2_2 (ite check_2_2 false (or exec_2_2_1 block_2_2_2))))\n"
    "\n"
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_3_1 () Bool)\n"
    "(declare-fun check_3_2 () Bool)\n"
    "\n"
    "(assert (= check_3_1 (and block_3_1_0 block_3_1_1 block_3_1_2)))\n"
    "(assert (= check_3_2 (and block_3_2_0 block_3_2_1 block_3_2_2)))\n"
    "\n"
    "; prevent scheduling of waiting threads\n"
    "(assert (=> (and block_3_1_0 (not check_3_1)) (not thread_3_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_3_1_1 (not check_3_1)) (not thread_3_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_3_1_2 (not check_3_1)) (not thread_3_2))) ; checkpoint 1: thread 2\n"
    "(assert (=> (and block_3_2_0 (not check_3_2)) (not thread_3_0))) ; checkpoint 2: thread 0\n"
    "(assert (=> (and block_3_2_1 (not check_3_2)) (not thread_3_1))) ; checkpoint 2: thread 1\n"
    "(assert (=> (and block_3_2_2 (not check_3_2)) (not thread_3_2))) ; checkpoint 2: thread 2\n\n",
    encoder->formula.str());

  /* two identical checkpoints */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("CHECK", 1));

  reset_encoder(0, 3);

  encoder->add_checkpoint_constraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_3_1_0 () Bool)\n"
    "(declare-fun block_3_1_1 () Bool)\n"
    "(declare-fun block_3_1_2 () Bool)\n"
    "(declare-fun block_3_2_0 () Bool)\n"
    "(declare-fun block_3_2_1 () Bool)\n"
    "(declare-fun block_3_2_2 () Bool)\n"
    "\n"
    "(assert (= block_3_1_0 (ite check_2_1 false (or exec_2_0_0 exec_2_0_2 block_2_1_0))))\n"
    "(assert (= block_3_1_1 (ite check_2_1 false (or exec_2_1_0 exec_2_1_2 block_2_1_1))))\n"
    "(assert (= block_3_1_2 (ite check_2_1 false (or exec_2_2_0 exec_2_2_2 block_2_1_2))))\n"
    "(assert (= block_3_2_0 (ite check_2_2 false (or exec_2_0_1 block_2_2_0))))\n"
    "(assert (= block_3_2_1 (ite check_2_2 false (or exec_2_1_1 block_2_2_1))))\n"
    "(assert (= block_3_2_2 (ite check_2_2 false (or exec_2_2_1 block_2_2_2))))\n"
    "\n"
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_3_1 () Bool)\n"
    "(declare-fun check_3_2 () Bool)\n"
    "\n"
    "(assert (= check_3_1 (and block_3_1_0 block_3_1_1 block_3_1_2)))\n"
    "(assert (= check_3_2 (and block_3_2_0 block_3_2_1 block_3_2_2)))\n"
    "\n"
    "; prevent scheduling of waiting threads\n"
    "(assert (=> (and block_3_1_0 (not check_3_1)) (not thread_3_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_3_1_1 (not check_3_1)) (not thread_3_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_3_1_2 (not check_3_1)) (not thread_3_2))) ; checkpoint 1: thread 2\n"
    "(assert (=> (and block_3_2_0 (not check_3_2)) (not thread_3_0))) ; checkpoint 2: thread 0\n"
    "(assert (=> (and block_3_2_1 (not check_3_2)) (not thread_3_1))) ; checkpoint 2: thread 1\n"
    "(assert (=> (and block_3_2_2 (not check_3_2)) (not thread_3_2))) ; checkpoint 2: thread 2\n\n",
    encoder->formula.str());

  /* verbosity */
  for (const auto & p : programs)
    p->erase(p->begin() + 1, p->end());

  ASSERT_EQ(programs[0]->size(), 1);

  reset_encoder(0, 2);

  verbose = false;
  encoder->add_checkpoint_constraints();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun block_2_1_0 () Bool)\n"
    "(declare-fun block_2_1_1 () Bool)\n"
    "(declare-fun block_2_1_2 () Bool)\n"
    "\n"
    "(assert (= block_2_1_0 exec_1_0_0))\n"
    "(assert (= block_2_1_1 exec_1_1_0))\n"
    "(assert (= block_2_1_2 exec_1_2_0))\n"
    "\n"
    "(declare-fun check_2_1 () Bool)\n"
    "\n"
    "(assert (= check_2_1 (and block_2_1_0 block_2_1_1 block_2_1_2)))\n"
    "\n"
    "(assert (=> (and block_2_1_0 (not check_2_1)) (not thread_2_0)))\n"
    "(assert (=> (and block_2_1_1 (not check_2_1)) (not thread_2_1)))\n"
    "(assert (=> (and block_2_1_2 (not check_2_1)) (not thread_2_2)))\n\n",
    encoder->formula.str());
}

// void add_statement_execution (void);
TEST_F(SMTLibEncoderTest, add_statement_execution)
{
  add_dummy_programs(3, 3);

  encoder->step = 1;

  encoder->add_statement_execution();

  ASSERT_EQ(
    "; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;\n"
    "\n"
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_1_0_0 () Bool)\n"
    "(declare-fun exec_1_0_1 () Bool)\n"
    "(declare-fun exec_1_0_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_1_0 () Bool)\n"
    "(declare-fun exec_1_1_1 () Bool)\n"
    "(declare-fun exec_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "(declare-fun exec_1_2_1 () Bool)\n"
    "(declare-fun exec_1_2_2 () Bool)\n"
    "\n"
    "(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))\n"
    "(assert (= exec_1_0_1 (and stmt_1_0_1 thread_1_0)))\n"
    "(assert (= exec_1_0_2 (and stmt_1_0_2 thread_1_0)))\n"
    "\n"
    "(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))\n"
    "(assert (= exec_1_1_1 (and stmt_1_1_1 thread_1_1)))\n"
    "(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))\n"
    "\n"
    "(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))\n"
    "(assert (= exec_1_2_1 (and stmt_1_2_1 thread_1_2)))\n"
    "(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))\n\n",
    encoder->formula.str());

  /* last statement is a checkpoint */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("CHECK", 1));

  reset_encoder(0, 1);

  encoder->add_statement_execution();

  ASSERT_EQ(
    "; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;\n"
    "\n"
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_1_0_0 () Bool)\n"
    "(declare-fun exec_1_0_1 () Bool)\n"
    "(declare-fun exec_1_0_2 () Bool)\n"
    "(declare-fun exec_1_0_3 () Bool)\n"
    "\n"
    "(declare-fun exec_1_1_0 () Bool)\n"
    "(declare-fun exec_1_1_1 () Bool)\n"
    "(declare-fun exec_1_1_2 () Bool)\n"
    "(declare-fun exec_1_1_3 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "(declare-fun exec_1_2_1 () Bool)\n"
    "(declare-fun exec_1_2_2 () Bool)\n"
    "(declare-fun exec_1_2_3 () Bool)\n"
    "\n"
    "(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))\n"
    "(assert (= exec_1_0_1 (and stmt_1_0_1 thread_1_0)))\n"
    "(assert (= exec_1_0_2 (and stmt_1_0_2 thread_1_0)))\n"
    "(assert (= exec_1_0_3 (and stmt_1_0_3 thread_1_0)))\n"
    "\n"
    "(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))\n"
    "(assert (= exec_1_1_1 (and stmt_1_1_1 thread_1_1)))\n"
    "(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))\n"
    "(assert (= exec_1_1_3 (and stmt_1_1_3 thread_1_1)))\n"
    "\n"
    "(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))\n"
    "(assert (= exec_1_2_1 (and stmt_1_2_1 thread_1_2)))\n"
    "(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))\n"
    "(assert (= exec_1_2_3 (and stmt_1_2_3 thread_1_2)))\n\n",
    encoder->formula.str());

  /* verbosity */
  for (const auto & p : programs)
    p->erase(p->begin() + 1, p->end());

  reset_encoder(0, 1);

  verbose = false;
  encoder->add_statement_execution();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun exec_1_0_0 () Bool)\n"
    "\n"
    "(declare-fun exec_1_1_0 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "\n"
    "(assert (= exec_1_0_0 (and stmt_1_0_0 thread_1_0)))\n"
    "\n"
    "(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))\n"
    "\n"
    "(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))\n\n",
    encoder->formula.str());
}

// string load(Load &);
TEST_F(SMTLibEncoderTest, load)
{
  Load l = Load(1);

  encoder->step = 1;

  ASSERT_EQ("(select heap_0 #x0001)", encoder->load(l));

  /* indirect */
  l.indirect = true;

  ASSERT_EQ("(select heap_0 (select heap_0 #x0001))", encoder->load(l));
}

// virtual void encode (void);
TEST_F(SMTLibEncoderTest, encode)
{
  add_dummy_programs(3, 3);

  encoder->SMTLibEncoder::encode();

  ASSERT_EQ(
    "(set-logic QF_AUFBV)\n"
    "\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; initial state\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(0, 0);

  verbose = false;
  encoder->SMTLibEncoder::encode();
  verbose = true;

  ASSERT_EQ(
    "(set-logic QF_AUFBV)\n"
    "\n"
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n"
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder->formula.str());
}
