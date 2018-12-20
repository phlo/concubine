#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct SMTLibEncoderTest : public ::testing::Test
{
  const char *      expected;

  ProgramList       programs;
  SMTLibEncoderPtr  encoder = create_encoder(0);

  SMTLibEncoderPtr create_encoder (const word bound)
    {
        return make_shared<SMTLibEncoderFunctional>(
          make_shared<ProgramList>(programs),
          bound);
    }

  void reset_encoder (const word bound, unsigned long step)
    {
      encoder = create_encoder(bound);
      encoder->step = step;
    }

  void add_dummy_programs (unsigned num, unsigned size)
    {
      InstructionPtr op = Instruction::Set::create("ADDI", 1);
      for (size_t i = 0; i < num; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));
          for (size_t j = 0; j < size; j++)
            programs[i]->add(op);
        }

      encoder = create_encoder(0);
    }
};

// string heap_var (const word);
TEST_F(SMTLibEncoderTest, heap_var_args)
{
  ASSERT_STREQ("heap_0", encoder->heap_var(0).c_str());
  ASSERT_STREQ("heap_1", encoder->heap_var(1).c_str());
  ASSERT_STREQ("heap_2", encoder->heap_var(2).c_str());
}

// string heap_var (void);
TEST_F(SMTLibEncoderTest, heap_var)
{
  ASSERT_STREQ("heap_0", encoder->heap_var().c_str());

  encoder->step = 1;
  ASSERT_STREQ("heap_1", encoder->heap_var().c_str());

  encoder->step = 2;
  ASSERT_STREQ("heap_2", encoder->heap_var().c_str());
}

// string accu_var (const word, const word);
TEST_F(SMTLibEncoderTest, accu_var_args)
{
  ASSERT_STREQ("accu_0_1", encoder->accu_var(0, 1).c_str());
  ASSERT_STREQ("accu_1_2", encoder->accu_var(1, 2).c_str());
  ASSERT_STREQ("accu_2_3", encoder->accu_var(2, 3).c_str());
}

// string accu_var (void);
TEST_F(SMTLibEncoderTest, accu_var)
{
  encoder->thread = 1;
  ASSERT_STREQ("accu_0_1", encoder->accu_var().c_str());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_STREQ("accu_1_2", encoder->accu_var().c_str());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_STREQ("accu_2_3", encoder->accu_var().c_str());
}

// string mem_var (const word, const word);
TEST_F(SMTLibEncoderTest, mem_var_args)
{
  ASSERT_STREQ("mem_0_1", encoder->mem_var(0, 1).c_str());
  ASSERT_STREQ("mem_1_2", encoder->mem_var(1, 2).c_str());
  ASSERT_STREQ("mem_2_3", encoder->mem_var(2, 3).c_str());
}

// string mem_var (void);
TEST_F(SMTLibEncoderTest, mem_var)
{
  encoder->thread = 1;
  ASSERT_STREQ("mem_0_1", encoder->mem_var().c_str());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_STREQ("mem_1_2", encoder->mem_var().c_str());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_STREQ("mem_2_3", encoder->mem_var().c_str());
}

// string stmt_var (const word, const word, const word);
TEST_F(SMTLibEncoderTest, stmt_var_args)
{
  ASSERT_STREQ("stmt_0_1_2", encoder->stmt_var(0, 1, 2).c_str());
  ASSERT_STREQ("stmt_1_2_3", encoder->stmt_var(1, 2, 3).c_str());
  ASSERT_STREQ("stmt_2_3_4", encoder->stmt_var(2, 3, 4).c_str());
}

// string stmt_var (void);
TEST_F(SMTLibEncoderTest, stmt_var)
{
  encoder->thread = 1;
  encoder->pc = 2;
  ASSERT_STREQ("stmt_0_1_2", encoder->stmt_var().c_str());

  encoder->step = 1;
  encoder->thread = 2;
  encoder->pc = 3;
  ASSERT_STREQ("stmt_1_2_3", encoder->stmt_var().c_str());

  encoder->step = 2;
  encoder->thread = 3;
  encoder->pc = 4;
  ASSERT_STREQ("stmt_2_3_4", encoder->stmt_var().c_str());
}

// string thread_var (const word, const word);
TEST_F(SMTLibEncoderTest, thread_var_args)
{
  ASSERT_STREQ("thread_0_1", encoder->thread_var(0, 1).c_str());
  ASSERT_STREQ("thread_1_2", encoder->thread_var(1, 2).c_str());
  ASSERT_STREQ("thread_2_3", encoder->thread_var(2, 3).c_str());
}

// string thread_var (void);
TEST_F(SMTLibEncoderTest, thread_var)
{
  encoder->thread = 1;
  ASSERT_STREQ("thread_0_1", encoder->thread_var().c_str());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_STREQ("thread_1_2", encoder->thread_var().c_str());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_STREQ("thread_2_3", encoder->thread_var().c_str());
}

// string exec_var (const word, const word, const word);
TEST_F(SMTLibEncoderTest, exec_var_args)
{
  ASSERT_STREQ("exec_0_1_2", encoder->exec_var(0, 1, 2).c_str());
  ASSERT_STREQ("exec_1_2_3", encoder->exec_var(1, 2, 3).c_str());
  ASSERT_STREQ("exec_2_3_4", encoder->exec_var(2, 3, 4).c_str());
}

// string exec_var (void);
TEST_F(SMTLibEncoderTest, exec_var)
{
  encoder->thread = 1;
  encoder->pc = 2;
  ASSERT_STREQ("exec_0_1_2", encoder->exec_var().c_str());

  encoder->step = 1;
  encoder->thread = 2;
  encoder->pc = 3;
  ASSERT_STREQ("exec_1_2_3", encoder->exec_var().c_str());

  encoder->step = 2;
  encoder->thread = 3;
  encoder->pc = 4;
  ASSERT_STREQ("exec_2_3_4", encoder->exec_var().c_str());
}

// string cas_var (const word, const word);
TEST_F(SMTLibEncoderTest, cas_var_args)
{
  ASSERT_STREQ("cas_0_1", encoder->cas_var(0, 1).c_str());
  ASSERT_STREQ("cas_1_2", encoder->cas_var(1, 2).c_str());
  ASSERT_STREQ("cas_2_3", encoder->cas_var(2, 3).c_str());
}

// string cas_var (void);
TEST_F(SMTLibEncoderTest, cas_var)
{
  encoder->thread = 1;
  ASSERT_STREQ("cas_0_1", encoder->cas_var().c_str());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_STREQ("cas_1_2", encoder->cas_var().c_str());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_STREQ("cas_2_3", encoder->cas_var().c_str());
}

// string sync_var (const word, const word);
TEST_F(SMTLibEncoderTest, sync_var_args)
{
  ASSERT_STREQ("sync_0_1", encoder->sync_var(0, 1).c_str());
  ASSERT_STREQ("sync_1_2", encoder->sync_var(1, 2).c_str());
  ASSERT_STREQ("sync_2_3", encoder->sync_var(2, 3).c_str());
}

// string exit_var (const word);
TEST_F(SMTLibEncoderTest, exit_var_args)
{
  ASSERT_STREQ("exit_0", encoder->exit_var(0).c_str());
  ASSERT_STREQ("exit_1", encoder->exit_var(1).c_str());
  ASSERT_STREQ("exit_2", encoder->exit_var(2).c_str());
}

// string exit_var (void);
TEST_F(SMTLibEncoderTest, exit_var)
{
  encoder->thread = 1;
  ASSERT_STREQ("exit_0", encoder->exit_var().c_str());

  encoder->step = 1;
  ASSERT_STREQ("exit_1", encoder->exit_var().c_str());

  encoder->step = 2;
  ASSERT_STREQ("exit_2", encoder->exit_var().c_str());
}

// void declare_heap_var (void);
TEST_F(SMTLibEncoderTest, declare_heap_var)
{
  encoder->declare_heap_var();

  expected =
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_accu_vars (void);
TEST_F(SMTLibEncoderTest, declare_accu_vars)
{
  add_dummy_programs(3, 3);

  /* step 0 */
  encoder->declare_accu_vars();

  expected =
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "(declare-fun accu_0_3 () (_ BitVec 16))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_accu_vars();

  expected =
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "(declare-fun accu_1_3 () (_ BitVec 16))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_accu_vars();
  verbose = true;

  expected =
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "(declare-fun accu_0_3 () (_ BitVec 16))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_mem_vars (void);
TEST_F(SMTLibEncoderTest, declare_mem_vars)
{
  add_dummy_programs(3, 3);

  /* step 0 */
  encoder->declare_mem_vars();

  expected =
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "(declare-fun mem_0_3 () (_ BitVec 16))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_mem_vars();

  expected =
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "(declare-fun mem_1_3 () (_ BitVec 16))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_mem_vars();
  verbose = true;

  expected =
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "(declare-fun mem_0_3 () (_ BitVec 16))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_stmt_vars (void);
TEST_F(SMTLibEncoderTest, declare_stmt_vars)
{
  add_dummy_programs(3, 3);

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_stmt_vars();

  expected =
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
    "(declare-fun stmt_1_3_2 () Bool)\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_stmt_vars();

  expected =
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

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_stmt_vars();
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
    "(declare-fun stmt_1_3_2 () Bool)\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_thread_vars (void);
TEST_F(SMTLibEncoderTest, declare_thread_vars)
{
  add_dummy_programs(3, 3);

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_thread_vars();

  expected =
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_thread_vars();

  expected =
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n"
    "(declare-fun thread_2_3 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_thread_vars();
  verbose = true;

  expected =
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "(declare-fun thread_1_3 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_exec_vars (void);
TEST_F(SMTLibEncoderTest, declare_exec_vars)
{
  add_dummy_programs(3, 3);

  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_exec_vars();

  expected =
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_1_1_0 () Bool)\n"
    "(declare-fun exec_1_1_1 () Bool)\n"
    "(declare-fun exec_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "(declare-fun exec_1_2_1 () Bool)\n"
    "(declare-fun exec_1_2_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_3_0 () Bool)\n"
    "(declare-fun exec_1_3_1 () Bool)\n"
    "(declare-fun exec_1_3_2 () Bool)\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_exec_vars();

  expected =
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_2_1_0 () Bool)\n"
    "(declare-fun exec_2_1_1 () Bool)\n"
    "(declare-fun exec_2_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_2_2_0 () Bool)\n"
    "(declare-fun exec_2_2_1 () Bool)\n"
    "(declare-fun exec_2_2_2 () Bool)\n"
    "\n"
    "(declare-fun exec_2_3_0 () Bool)\n"
    "(declare-fun exec_2_3_1 () Bool)\n"
    "(declare-fun exec_2_3_2 () Bool)\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_exec_vars();
  verbose = true;

  expected =
    "(declare-fun exec_1_1_0 () Bool)\n"
    "(declare-fun exec_1_1_1 () Bool)\n"
    "(declare-fun exec_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "(declare-fun exec_1_2_1 () Bool)\n"
    "(declare-fun exec_1_2_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_3_0 () Bool)\n"
    "(declare-fun exec_1_3_1 () Bool)\n"
    "(declare-fun exec_1_3_2 () Bool)\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_cas_vars (void);
TEST_F(SMTLibEncoderTest, declare_cas_vars)
{
  add_dummy_programs(3, 3);

  /* no CAS statement */
  encoder->declare_cas_vars();

  ASSERT_STREQ("", encoder->formula.str().c_str());

  /* single CAS in thread 1 */
  programs[0]->add(Instruction::Set::create("CAS", 0));

  reset_encoder(0, 1);

  encoder->declare_cas_vars();

  expected =
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_1 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* 1 CAS per thread */
  for (size_t i = 1; i < 3; i++)
    programs[i]->add(Instruction::Set::create("CAS", 0));

  reset_encoder(0, 1);

  encoder->declare_cas_vars();

  expected =
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_1 () Bool)\n"
    "(declare-fun cas_1_2 () Bool)\n"
    "(declare-fun cas_1_3 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_cas_vars();

  expected =
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_2_1 () Bool)\n"
    "(declare-fun cas_2_2 () Bool)\n"
    "(declare-fun cas_2_3 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_cas_vars();
  verbose = true;

  expected =
    "(declare-fun cas_1_1 () Bool)\n"
    "(declare-fun cas_1_2 () Bool)\n"
    "(declare-fun cas_1_3 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_sync_vars (void);
TEST_F(SMTLibEncoderTest, declare_sync_vars)
{
  add_dummy_programs(3, 3);

  word sync_id = 1;

  /* 3 different sync ids */
  for (size_t i = 0; i < 3; i++)
    programs[i]->add(Instruction::Set::create("SYNC", sync_id++));

  reset_encoder(0, 1);

  encoder->declare_sync_vars();

  expected =
    "; sync variables - sync_<step>_<id>\n"
    "(declare-fun sync_1_1 () Bool)\n"
    "(declare-fun sync_1_2 () Bool)\n"
    "(declare-fun sync_1_3 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* same sync ids */
  for (size_t i = 0; i < 3; i++)
    programs[i]->add(Instruction::Set::create("SYNC", sync_id));

  reset_encoder(0, 1);

  encoder->declare_sync_vars();

  expected =
    "; sync variables - sync_<step>_<id>\n"
    "(declare-fun sync_1_1 () Bool)\n"
    "(declare-fun sync_1_2 () Bool)\n"
    "(declare-fun sync_1_3 () Bool)\n"
    "(declare-fun sync_1_4 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_sync_vars();

  expected =
    "; sync variables - sync_<step>_<id>\n"
    "(declare-fun sync_2_1 () Bool)\n"
    "(declare-fun sync_2_2 () Bool)\n"
    "(declare-fun sync_2_3 () Bool)\n"
    "(declare-fun sync_2_4 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_sync_vars();
  verbose = true;

  expected =
    "(declare-fun sync_1_1 () Bool)\n"
    "(declare-fun sync_1_2 () Bool)\n"
    "(declare-fun sync_1_3 () Bool)\n"
    "(declare-fun sync_1_4 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void declare_exit_var (void);
TEST_F(SMTLibEncoderTest, declare_exit_vars)
{
  /* step 1 */
  reset_encoder(0, 1);

  encoder->declare_exit_var();

  expected =
    "; exit variable - exit_<step>\n"
    "(declare-fun exit_1 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* step 2 */
  reset_encoder(0, 2);

  encoder->declare_exit_var();

  expected =
    "; exit variable - exit_<step>\n"
    "(declare-fun exit_2 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_exit_var();
  verbose = true;

  expected =
    "(declare-fun exit_1 () Bool)\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// string assign_var (string, string);
TEST_F(SMTLibEncoderTest, assign_var)
{
  ASSERT_STREQ(
    "(assert (= foo bar))",
    encoder->assign_var("foo", "bar").c_str());
}

// void add_initial_state (void);
TEST_F(SMTLibEncoderTest, add_initial_state)
{
  add_dummy_programs(3, 3);

  encoder->add_initial_state();

  expected =
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; initial state\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "(declare-fun accu_0_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "(assert (= accu_0_3 #x0000))\n"
    "\n"
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "(declare-fun mem_0_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "(assert (= mem_0_3 #x0000))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 0);

  verbose = false;
  encoder->add_initial_state();
  verbose = true;

  expected =
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "(declare-fun accu_0_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "(assert (= accu_0_3 #x0000))\n"
    "\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "(declare-fun mem_0_3 () (_ BitVec 16))\n"
    "\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "(assert (= mem_0_3 #x0000))\n"
    "\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void add_initial_statement_activation (void);
TEST_F(SMTLibEncoderTest, add_initial_statement_activation)
{
  add_dummy_programs(3, 3);

  encoder->step = 1;

  encoder->add_initial_statement_activation();

  expected =
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

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  reset_encoder(0, 1);

  verbose = false;
  encoder->add_initial_statement_activation();
  verbose = true;

  expected =
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

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void add_synchronization_constraints (void);
TEST_F(SMTLibEncoderTest, add_synchronization_constraints)
{
  /* single sync barrier */
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));
      programs[i]->add(Instruction::Set::create("SYNC", 1));
    }

  reset_encoder(0, 1);

  encoder->add_synchronization_constraints();

  expected =
    "; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; sync variables - sync_<step>_<id>\n"
    "(declare-fun sync_1_1 () Bool)\n"
    "\n"
    "; all threads synchronized?\n"
    "(assert (= sync_1_1 (and stmt_1_1_0 stmt_1_2_0 stmt_1_3_0 (or thread_1_1 thread_1_2 thread_1_3))))\n"
    "\n"
    "; prevent scheduling of waiting threads\n"
    "(assert (=> (and stmt_1_1_0 (or (not stmt_1_2_0) (not stmt_1_3_0))) (not thread_1_1))) ; barrier 1: thread 1\n"
    "(assert (=> (and stmt_1_2_0 (or (not stmt_1_1_0) (not stmt_1_3_0))) (not thread_1_2))) ; barrier 1: thread 2\n"
    "(assert (=> (and stmt_1_3_0 (or (not stmt_1_1_0) (not stmt_1_2_0))) (not thread_1_3))) ; barrier 1: thread 3\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* two different barriers */
  for (const auto & p : programs)
    p->add(Instruction::Set::create("SYNC", 2));

  reset_encoder(0, 1);

  encoder->add_synchronization_constraints();

  expected =
    "; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; sync variables - sync_<step>_<id>\n"
    "(declare-fun sync_1_1 () Bool)\n"
    "(declare-fun sync_1_2 () Bool)\n"
    "\n"
    "; all threads synchronized?\n"
    "(assert (= sync_1_1 (and stmt_1_1_0 stmt_1_2_0 stmt_1_3_0 (or thread_1_1 thread_1_2 thread_1_3))))\n"
    "(assert (= sync_1_2 (and stmt_1_1_1 stmt_1_2_1 stmt_1_3_1 (or thread_1_1 thread_1_2 thread_1_3))))\n"
    "\n"
    "; prevent scheduling of waiting threads\n"
    "(assert (=> (and stmt_1_1_0 (or (not stmt_1_2_0) (not stmt_1_3_0))) (not thread_1_1))) ; barrier 1: thread 1\n"
    "(assert (=> (and stmt_1_2_0 (or (not stmt_1_1_0) (not stmt_1_3_0))) (not thread_1_2))) ; barrier 1: thread 2\n"
    "(assert (=> (and stmt_1_3_0 (or (not stmt_1_1_0) (not stmt_1_2_0))) (not thread_1_3))) ; barrier 1: thread 3\n"
    "(assert (=> (and stmt_1_1_1 (or (not stmt_1_2_1) (not stmt_1_3_1))) (not thread_1_1))) ; barrier 2: thread 1\n"
    "(assert (=> (and stmt_1_2_1 (or (not stmt_1_1_1) (not stmt_1_3_1))) (not thread_1_2))) ; barrier 2: thread 2\n"
    "(assert (=> (and stmt_1_3_1 (or (not stmt_1_1_1) (not stmt_1_2_1))) (not thread_1_3))) ; barrier 2: thread 3\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* two identical barriers */
  for (const auto & p : programs)
    p->add(Instruction::Set::create("SYNC", 1));

  reset_encoder(0, 1);

  encoder->add_synchronization_constraints();

  expected =
    "; synchronization constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; sync variables - sync_<step>_<id>\n"
    "(declare-fun sync_1_1 () Bool)\n"
    "(declare-fun sync_1_2 () Bool)\n"
    "\n"
    "; all threads synchronized?\n"
    "(assert (= sync_1_1 (and (or stmt_1_1_0 stmt_1_1_2) (or stmt_1_2_0 stmt_1_2_2) (or stmt_1_3_0 stmt_1_3_2) (or thread_1_1 thread_1_2 thread_1_3))))\n"
    "(assert (= sync_1_2 (and stmt_1_1_1 stmt_1_2_1 stmt_1_3_1 (or thread_1_1 thread_1_2 thread_1_3))))\n"
    "\n"
    "; prevent scheduling of waiting threads\n"
    "(assert (=> (and (or stmt_1_1_0 stmt_1_1_2) (or (not stmt_1_2_0) (not stmt_1_2_2) (not stmt_1_3_0) (not stmt_1_3_2))) (not thread_1_1))) ; barrier 1: thread 1\n"
    "(assert (=> (and (or stmt_1_2_0 stmt_1_2_2) (or (not stmt_1_1_0) (not stmt_1_1_2) (not stmt_1_3_0) (not stmt_1_3_2))) (not thread_1_2))) ; barrier 1: thread 2\n"
    "(assert (=> (and (or stmt_1_3_0 stmt_1_3_2) (or (not stmt_1_1_0) (not stmt_1_1_2) (not stmt_1_2_0) (not stmt_1_2_2))) (not thread_1_3))) ; barrier 1: thread 3\n"
    "(assert (=> (and stmt_1_1_1 (or (not stmt_1_2_1) (not stmt_1_3_1))) (not thread_1_1))) ; barrier 2: thread 1\n"
    "(assert (=> (and stmt_1_2_1 (or (not stmt_1_1_1) (not stmt_1_3_1))) (not thread_1_2))) ; barrier 2: thread 2\n"
    "(assert (=> (and stmt_1_3_1 (or (not stmt_1_1_1) (not stmt_1_2_1))) (not thread_1_3))) ; barrier 2: thread 3\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  for (const auto & p : programs)
    p->erase(p->begin() + 1, p->end());

  ASSERT_EQ(programs[0]->size(), 1);

  reset_encoder(0, 1);

  verbose = false;
  encoder->add_synchronization_constraints();
  verbose = true;

  expected =
    "(declare-fun sync_1_1 () Bool)\n"
    "\n"
    "(assert (= sync_1_1 (and stmt_1_1_0 stmt_1_2_0 stmt_1_3_0 (or thread_1_1 thread_1_2 thread_1_3))))\n"
    "\n"
    "(assert (=> (and stmt_1_1_0 (or (not stmt_1_2_0) (not stmt_1_3_0))) (not thread_1_1)))\n"
    "(assert (=> (and stmt_1_2_0 (or (not stmt_1_1_0) (not stmt_1_3_0))) (not thread_1_2)))\n"
    "(assert (=> (and stmt_1_3_0 (or (not stmt_1_1_0) (not stmt_1_2_0))) (not thread_1_3)))\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// void add_statement_execution (void);
TEST_F(SMTLibEncoderTest, add_statement_execution)
{
  /* base case */
  add_dummy_programs(3, 3);

  encoder->step = 1;

  encoder->add_statement_execution();

  expected =
    "; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;\n"
    "\n"
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_1_1_0 () Bool)\n"
    "(declare-fun exec_1_1_1 () Bool)\n"
    "(declare-fun exec_1_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "(declare-fun exec_1_2_1 () Bool)\n"
    "(declare-fun exec_1_2_2 () Bool)\n"
    "\n"
    "(declare-fun exec_1_3_0 () Bool)\n"
    "(declare-fun exec_1_3_1 () Bool)\n"
    "(declare-fun exec_1_3_2 () Bool)\n"
    "\n"
    "(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))\n"
    "(assert (= exec_1_1_1 (and stmt_1_1_1 thread_1_1)))\n"
    "(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))\n"
    "\n"
    "(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))\n"
    "(assert (= exec_1_2_1 (and stmt_1_2_1 thread_1_2)))\n"
    "(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))\n"
    "\n"
    "(assert (= exec_1_3_0 (and stmt_1_3_0 thread_1_3)))\n"
    "(assert (= exec_1_3_1 (and stmt_1_3_1 thread_1_3)))\n"
    "(assert (= exec_1_3_2 (and stmt_1_3_2 thread_1_3)))\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* last statement is a sync barrier */
  for (const auto & p : programs)
    p->add(Instruction::Set::create("SYNC", 1));

  reset_encoder(0, 1);

  encoder->add_statement_execution();

  expected =
    "; statement execution - shorthand for statement & thread activation ;;;;;;;;;;;;\n"
    "\n"
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
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
    "(declare-fun exec_1_3_0 () Bool)\n"
    "(declare-fun exec_1_3_1 () Bool)\n"
    "(declare-fun exec_1_3_2 () Bool)\n"
    "(declare-fun exec_1_3_3 () Bool)\n"
    "\n"
    "(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))\n"
    "(assert (= exec_1_1_1 (and stmt_1_1_1 thread_1_1)))\n"
    "(assert (= exec_1_1_2 (and stmt_1_1_2 thread_1_1)))\n"
    "(assert (= exec_1_1_3 (and stmt_1_1_3 sync_1_1)))\n"
    "\n"
    "(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))\n"
    "(assert (= exec_1_2_1 (and stmt_1_2_1 thread_1_2)))\n"
    "(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))\n"
    "(assert (= exec_1_2_3 (and stmt_1_2_3 sync_1_1)))\n"
    "\n"
    "(assert (= exec_1_3_0 (and stmt_1_3_0 thread_1_3)))\n"
    "(assert (= exec_1_3_1 (and stmt_1_3_1 thread_1_3)))\n"
    "(assert (= exec_1_3_2 (and stmt_1_3_2 thread_1_3)))\n"
    "(assert (= exec_1_3_3 (and stmt_1_3_3 sync_1_1)))\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());

  /* verbosity */
  for (const auto & p : programs)
    p->erase(p->begin() + 1, p->end());

  reset_encoder(0, 1);

  verbose = false;
  encoder->add_statement_execution();
  verbose = true;

  expected =
    "(declare-fun exec_1_1_0 () Bool)\n"
    "\n"
    "(declare-fun exec_1_2_0 () Bool)\n"
    "\n"
    "(declare-fun exec_1_3_0 () Bool)\n"
    "\n"
    "(assert (= exec_1_1_0 (and stmt_1_1_0 thread_1_1)))\n"
    "\n"
    "(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))\n"
    "\n"
    "(assert (= exec_1_3_0 (and stmt_1_3_0 thread_1_3)))\n\n";

  ASSERT_STREQ(expected, encoder->formula.str().c_str());
}

// TODO
// void add_comment_section (const std::string &);

// void add_comment_subsection (const std::string &);

// string load(Load &);

// virtual void encode (void);
