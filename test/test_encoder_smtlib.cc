#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct SMTLibEncoderTest : public ::testing::Test
{
  Program_list      programs;
  SMTLibEncoder_ptr encoder = create_encoder(0);

  Program_ptr create_program (string code)
    {
      string path = "dummy.asm";
      istringstream inbuf {code};
      return make_shared<Program>(inbuf, path);
    }

  SMTLibEncoder_ptr create_encoder (const word_t bound)
    {
      return make_shared<SMTLibEncoderFunctional>(
        make_shared<Program_list>(programs),
        bound,
        false);
    }

  void reset_encoder (const word_t bound, bound_t step)
    {
      encoder = create_encoder(bound);
      encoder->step = step;
    }

  void add_dummy_programs (unsigned num, unsigned size)
    {
      ostringstream code;
      const char * op = "ADDI 1\n";

      for (size_t i = 0; i < size; i++)
        code << op;

      for (size_t i = 0; i < num; i++)
        programs.push_back(create_program(code.str()));

      encoder = create_encoder(0);
    }
};

/* SMTLibEncoder::accu_var ****************************************************/
TEST_F(SMTLibEncoderTest, accu_var_args)
{
  ASSERT_EQ("accu_0_1", encoder->accu_var(0, 1));
  ASSERT_EQ("accu_1_2", encoder->accu_var(1, 2));
  ASSERT_EQ("accu_2_3", encoder->accu_var(2, 3));
}

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

/* SMTLibEncoder::mem_var *****************************************************/
TEST_F(SMTLibEncoderTest, mem_var_args)
{
  ASSERT_EQ("mem_0_1", encoder->mem_var(0, 1));
  ASSERT_EQ("mem_1_2", encoder->mem_var(1, 2));
  ASSERT_EQ("mem_2_3", encoder->mem_var(2, 3));
}

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

/* SMTLibEncoder::sb_adr_var **************************************************/
TEST_F(SMTLibEncoderTest, sb_adr_var_args)
{
  ASSERT_EQ("sb-adr_0_1", encoder->sb_adr_var(0, 1));
  ASSERT_EQ("sb-adr_1_2", encoder->sb_adr_var(1, 2));
  ASSERT_EQ("sb-adr_2_3", encoder->sb_adr_var(2, 3));
}

TEST_F(SMTLibEncoderTest, sb_adr_var)
{
  encoder->thread = 1;
  ASSERT_EQ("sb-adr_0_1", encoder->sb_adr_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("sb-adr_1_2", encoder->sb_adr_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("sb-adr_2_3", encoder->sb_adr_var());
}

/* SMTLibEncoder::sb_val_var **************************************************/
TEST_F(SMTLibEncoderTest, sb_val_var_args)
{
  ASSERT_EQ("sb-val_0_1", encoder->sb_val_var(0, 1));
  ASSERT_EQ("sb-val_1_2", encoder->sb_val_var(1, 2));
  ASSERT_EQ("sb-val_2_3", encoder->sb_val_var(2, 3));
}

TEST_F(SMTLibEncoderTest, sb_val_var)
{
  encoder->thread = 1;
  ASSERT_EQ("sb-val_0_1", encoder->sb_val_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("sb-val_1_2", encoder->sb_val_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("sb-val_2_3", encoder->sb_val_var());
}

/* SMTLibEncoder::sb_full_var *************************************************/
TEST_F(SMTLibEncoderTest, sb_full_var_args)
{
  ASSERT_EQ("sb-full_0_1", encoder->sb_full_var(0, 1));
  ASSERT_EQ("sb-full_1_2", encoder->sb_full_var(1, 2));
  ASSERT_EQ("sb-full_2_3", encoder->sb_full_var(2, 3));
}

TEST_F(SMTLibEncoderTest, sb_full_var)
{
  encoder->thread = 1;
  ASSERT_EQ("sb-full_0_1", encoder->sb_full_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("sb-full_1_2", encoder->sb_full_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("sb-full_2_3", encoder->sb_full_var());
}

/* SMTLibEncoder::heap_var ****************************************************/
TEST_F(SMTLibEncoderTest, heap_var_args)
{
  ASSERT_EQ("heap_0", encoder->heap_var(0));
  ASSERT_EQ("heap_1", encoder->heap_var(1));
  ASSERT_EQ("heap_2", encoder->heap_var(2));
}

TEST_F(SMTLibEncoderTest, heap_var)
{
  ASSERT_EQ("heap_0", encoder->heap_var());

  encoder->step = 1;
  ASSERT_EQ("heap_1", encoder->heap_var());

  encoder->step = 2;
  ASSERT_EQ("heap_2", encoder->heap_var());
}

/* SMTLibEncoder::thread_var **************************************************/
TEST_F(SMTLibEncoderTest, thread_var_args)
{
  ASSERT_EQ("thread_0_1", encoder->thread_var(0, 1));
  ASSERT_EQ("thread_1_2", encoder->thread_var(1, 2));
  ASSERT_EQ("thread_2_3", encoder->thread_var(2, 3));
}

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

/* SMTLibEncoder::flush_var ***************************************************/
TEST_F(SMTLibEncoderTest, flush_var_args)
{
  ASSERT_EQ("flush_0_1", encoder->flush_var(0, 1));
  ASSERT_EQ("flush_1_2", encoder->flush_var(1, 2));
  ASSERT_EQ("flush_2_3", encoder->flush_var(2, 3));
}

TEST_F(SMTLibEncoderTest, flush_var)
{
  encoder->thread = 1;
  ASSERT_EQ("flush_0_1", encoder->flush_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("flush_1_2", encoder->flush_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("flush_2_3", encoder->flush_var());
}

/* SMTLibEncoder::stmt_var ****************************************************/
TEST_F(SMTLibEncoderTest, stmt_var_args)
{
  ASSERT_EQ("stmt_0_1_2", encoder->stmt_var(0, 1, 2));
  ASSERT_EQ("stmt_1_2_3", encoder->stmt_var(1, 2, 3));
  ASSERT_EQ("stmt_2_3_4", encoder->stmt_var(2, 3, 4));
}

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

/* SMTLibEncoder::exec_var ****************************************************/
TEST_F(SMTLibEncoderTest, exec_var_args)
{
  ASSERT_EQ("exec_0_1_2", encoder->exec_var(0, 1, 2));
  ASSERT_EQ("exec_1_2_3", encoder->exec_var(1, 2, 3));
  ASSERT_EQ("exec_2_3_4", encoder->exec_var(2, 3, 4));
}

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

/* SMTLibEncoder::cas_var *****************************************************/
TEST_F(SMTLibEncoderTest, cas_var_args)
{
  ASSERT_EQ("cas_0_1", encoder->cas_var(0, 1));
  ASSERT_EQ("cas_1_2", encoder->cas_var(1, 2));
  ASSERT_EQ("cas_2_3", encoder->cas_var(2, 3));
}

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

/* SMTLibEncoder::block_var ***************************************************/
TEST_F(SMTLibEncoderTest, block_var_args)
{
  ASSERT_EQ("block_6_3_0", encoder->block_var(6, 3, 0));
  ASSERT_EQ("block_7_4_1", encoder->block_var(7, 4, 1));
  ASSERT_EQ("block_8_5_2", encoder->block_var(8, 5, 2));
}

TEST_F(SMTLibEncoderTest, check_var_args)
{
  ASSERT_EQ("check_0_1", encoder->check_var(0, 1));
  ASSERT_EQ("check_1_2", encoder->check_var(1, 2));
  ASSERT_EQ("check_2_3", encoder->check_var(2, 3));
}

/* SMTLibEncoder::exit_var ****************************************************/
TEST_F(SMTLibEncoderTest, exit_var_args)
{
  ASSERT_EQ("exit_0", encoder->exit_var(0));
  ASSERT_EQ("exit_1", encoder->exit_var(1));
  ASSERT_EQ("exit_2", encoder->exit_var(2));
}

TEST_F(SMTLibEncoderTest, exit_var)
{
  encoder->thread = 1;
  ASSERT_EQ("exit_0", encoder->exit_var());

  encoder->step = 1;
  ASSERT_EQ("exit_1", encoder->exit_var());

  encoder->step = 2;
  ASSERT_EQ("exit_2", encoder->exit_var());
}

/* SMTLibEncoder::declare_accu_vars *******************************************/
TEST_F(SMTLibEncoderTest, declare_accu_vars)
{
  add_dummy_programs(3, 3);

  // step 0
  encoder->declare_accu_vars();

  ASSERT_EQ(
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(0, 1);

  encoder->declare_accu_vars();

  ASSERT_EQ(
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_accu_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_mem_vars ********************************************/
TEST_F(SMTLibEncoderTest, declare_mem_vars)
{
  add_dummy_programs(3, 3);

  // step 0
  encoder->declare_mem_vars();

  ASSERT_EQ(
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(0, 1);

  encoder->declare_mem_vars();

  ASSERT_EQ(
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_mem_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_sb_adr_vars *****************************************/
TEST_F(SMTLibEncoderTest, declare_sb_adr_vars)
{
  add_dummy_programs(3, 3);

  // step 0
  encoder->declare_sb_adr_vars();

  ASSERT_EQ(
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(0, 1);

  encoder->declare_sb_adr_vars();

  ASSERT_EQ(
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_sb_adr_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_sb_val_vars *****************************************/
TEST_F(SMTLibEncoderTest, declare_sb_val_vars)
{
  add_dummy_programs(3, 3);

  // step 0
  encoder->declare_sb_val_vars();

  ASSERT_EQ(
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(0, 1);

  encoder->declare_sb_val_vars();

  ASSERT_EQ(
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_sb_val_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_sb_full_vars ****************************************/
TEST_F(SMTLibEncoderTest, declare_sb_full_vars)
{
  add_dummy_programs(3, 3);

  // step 0
  encoder->declare_sb_full_vars();

  ASSERT_EQ(
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(0, 1);

  encoder->declare_sb_full_vars();

  ASSERT_EQ(
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_1_0 () Bool)\n"
    "(declare-fun sb-full_1_1 () Bool)\n"
    "(declare-fun sb-full_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 0);

  verbose = false;
  encoder->declare_sb_full_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_heap_var ********************************************/
TEST_F(SMTLibEncoderTest, declare_heap_var)
{
  encoder->declare_heap_var();

  ASSERT_EQ(
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_thread_vars *****************************************/
TEST_F(SMTLibEncoderTest, declare_thread_vars)
{
  add_dummy_programs(3, 3);

  // step 1
  reset_encoder(0, 1);

  encoder->declare_thread_vars();

  ASSERT_EQ(
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->declare_thread_vars();

  ASSERT_EQ(
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_thread_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n",
    encoder->str());
}

/* SMTLibEncoder::declare_flush_vars ******************************************/
TEST_F(SMTLibEncoderTest, declare_flush_vars)
{
  add_dummy_programs(3, 3);

  // step 1
  reset_encoder(0, 1);

  encoder->declare_flush_vars();

  ASSERT_EQ(
    "; store buffer flush variables - flush_<step>_<thread>\n"
    "(declare-fun flush_1_0 () Bool)\n"
    "(declare-fun flush_1_1 () Bool)\n"
    "(declare-fun flush_1_2 () Bool)\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->declare_flush_vars();

  ASSERT_EQ(
    "; store buffer flush variables - flush_<step>_<thread>\n"
    "(declare-fun flush_2_0 () Bool)\n"
    "(declare-fun flush_2_1 () Bool)\n"
    "(declare-fun flush_2_2 () Bool)\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_flush_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun flush_1_0 () Bool)\n"
    "(declare-fun flush_1_1 () Bool)\n"
    "(declare-fun flush_1_2 () Bool)\n",
    encoder->str());
}

/* SMTLibEncoder::declare_stmt_vars *******************************************/
TEST_F(SMTLibEncoderTest, declare_stmt_vars)
{
  add_dummy_programs(3, 3);

  // step 1
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
    "(declare-fun stmt_1_2_2 () Bool)\n"
    "\n",
    encoder->str());

  // step 2
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
    "(declare-fun stmt_2_2_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(declare-fun stmt_1_2_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_exec_vars *******************************************/
TEST_F(SMTLibEncoderTest, declare_exec_vars)
{
  add_dummy_programs(3, 3);

  // step 1
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
    "(declare-fun exec_1_2_2 () Bool)\n"
    "\n",
    encoder->str());

  // step 2
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
    "(declare-fun exec_2_2_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(declare-fun exec_1_2_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_cas_vars ********************************************/
TEST_F(SMTLibEncoderTest, declare_cas_vars)
{
  add_dummy_programs(3, 3);

  // no CAS statement
  encoder->declare_cas_vars();

  ASSERT_EQ("", encoder->str());

  // single CAS in thread 1
  programs[0] = create_program(programs[0]->print() + "CAS 0\n");

  reset_encoder(0, 1);

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_0 () Bool)\n"
    "\n",
    encoder->str());

  // 1 CAS per thread
  programs[1] = create_program(programs[1]->print() + "CAS 0\n");
  programs[2] = create_program(programs[2]->print() + "CAS 0\n");

  reset_encoder(0, 1);

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_0 () Bool)\n"
    "(declare-fun cas_1_1 () Bool)\n"
    "(declare-fun cas_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_2_0 () Bool)\n"
    "(declare-fun cas_2_1 () Bool)\n"
    "(declare-fun cas_2_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_cas_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun cas_1_0 () Bool)\n"
    "(declare-fun cas_1_1 () Bool)\n"
    "(declare-fun cas_1_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_block_vars ******************************************/
TEST_F(SMTLibEncoderTest, declare_block_vars)
{
  add_dummy_programs(3, 3);

  // single checkpoint id
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 0\n");

  reset_encoder(0, 2);

  encoder->declare_block_vars();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_2_0_0 () Bool)\n"
    "(declare-fun block_2_0_1 () Bool)\n"
    "(declare-fun block_2_0_2 () Bool)\n"
    "\n",
    encoder->str());

  // two checkpoint ids
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 1\n");

  reset_encoder(0, 2);

  encoder->declare_block_vars();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_2_0_0 () Bool)\n"
    "(declare-fun block_2_0_1 () Bool)\n"
    "(declare-fun block_2_0_2 () Bool)\n"
    "(declare-fun block_2_1_0 () Bool)\n"
    "(declare-fun block_2_1_1 () Bool)\n"
    "(declare-fun block_2_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(declare-fun block_2_1_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_check_vars ******************************************/
TEST_F(SMTLibEncoderTest, declare_check_vars)
{
  add_dummy_programs(3, 3);

  word_t check_id = 1;

  // 3 different checkpoint ids
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK " + to_string(check_id++) + "\n");

  reset_encoder(0, 1);

  encoder->declare_check_vars();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "\n",
    encoder->str());

  // same checkpoint ids
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK " + to_string(check_id) + "\n");

  reset_encoder(0, 1);

  encoder->declare_check_vars();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n"
    "\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->declare_check_vars();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_2_1 () Bool)\n"
    "(declare-fun check_2_2 () Bool)\n"
    "(declare-fun check_2_3 () Bool)\n"
    "(declare-fun check_2_4 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_check_vars();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_exit_vars *******************************************/
TEST_F(SMTLibEncoderTest, declare_exit_vars)
{
  // step 1
  reset_encoder(0, 1);

  encoder->declare_exit_var();

  ASSERT_EQ(
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_1 () Bool)\n"
    "\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->declare_exit_var();

  ASSERT_EQ(
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 1);

  verbose = false;
  encoder->declare_exit_var();
  verbose = true;

  ASSERT_EQ("(declare-fun exit_1 () Bool)\n\n", encoder->str());
}

/* SMTLibEncoder::declare_exit_code *******************************************/
TEST_F(SMTLibEncoderTest, declare_exit_code)
{
  encoder->declare_exit_code();

  ASSERT_EQ(
    "(declare-fun exit-code () (_ BitVec 16))\n\n",
    encoder->str());
}

/* SMTLibEncoder::assign_var **************************************************/
TEST_F(SMTLibEncoderTest, assign_var)
{
  ASSERT_EQ("(assert (= foo bar))", encoder->assign_var("foo", "bar"));
}

/* SMTLibEncoder::add_initial_state *******************************************/
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
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n"
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n"
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_0_0 false))\n"
    "(assert (= sb-full_0_1 false))\n"
    "(assert (= sb-full_0_2 false))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n"
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n"
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_0_0 false))\n"
    "(assert (= sb-full_0_1 false))\n"
    "(assert (= sb-full_0_2 false))\n"
    "\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::add_initial_statement_activation ****************************/
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
    "(assert (not stmt_1_2_2))\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(assert (not stmt_1_2_2))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::add_exit_flag ***********************************************/
TEST_F(SMTLibEncoderTest, add_exit_flag)
{
  // no call to EXIT in step 2
  add_dummy_programs(3, 2);

  encoder->add_exit_flag();

  ASSERT_EQ("", encoder->str());

  // step 1
  programs.clear();

  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("EXIT " + to_string(i) + "\n"));

  reset_encoder(3, 1);

  encoder->add_exit_flag();

  ASSERT_EQ("", encoder->str());

  // step 2
  reset_encoder(3, 2);

  encoder->add_exit_flag();

  ASSERT_EQ(
    "; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_2 () Bool)\n"
    "\n"
    "(assert (= exit_2 (or exec_1_0_0 exec_1_1_0 exec_1_2_0)))\n"
    "\n",
    encoder->str());

  // step 3 - reached bound
  reset_encoder(3, 3);

  encoder->add_exit_flag();

  ASSERT_EQ(
    "; exit flag ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (= exit_3 (or exit_2 exec_2_0_0 exec_2_1_0 exec_2_2_0)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(3, 3);

  verbose = false;
  encoder->add_exit_flag();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun exit_3 () Bool)\n"
    "\n"
    "(assert (= exit_3 (or exit_2 exec_2_0_0 exec_2_1_0 exec_2_2_0)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::add_thread_scheduling ***************************************/
TEST_F(SMTLibEncoderTest, add_thread_scheduling)
{
  programs.push_back(create_program("EXIT 1"));
  programs.push_back(create_program("EXIT 1"));

  // step 1
  reset_encoder(0, 1);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "\n"
    "; cardinality constraint\n"
    "(assert (xor thread_1_0 thread_1_1))\n"
    "\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "\n"
    "; cardinality constraint\n"
    "(assert (or thread_2_0 thread_2_1 exit_2))\n"
    "(assert (or (not thread_2_0) (not thread_2_1)))\n"
    "(assert (or (not thread_2_0) (not exit_2)))\n"
    "(assert (or (not thread_2_1) (not exit_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 2);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "\n"
    "(assert (or thread_2_0 thread_2_1 exit_2))\n"
    "(assert (or (not thread_2_0) (not thread_2_1)))\n"
    "(assert (or (not thread_2_0) (not exit_2)))\n"
    "(assert (or (not thread_2_1) (not exit_2)))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderTest, add_thread_scheduling_single_thread)
{
  programs.push_back(create_program("EXIT 1"));

  // step 1
  reset_encoder(0, 1);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "\n"
    "; cardinality constraint\n"
    "(assert thread_1_0)\n"
    "\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_0 () Bool)\n"
    "\n"
    "; cardinality constraint\n"
    "(assert (xor thread_2_0 exit_2))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 2);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_2_0 () Bool)\n"
    "\n"
    "(assert (xor thread_2_0 exit_2))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderTest, add_thread_scheduling_store_buffer_constraints)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "STORE 1\n"
      "FENCE\n"
      "CAS 1\n"
    ));

  reset_encoder(0, 1);

  encoder->add_thread_scheduling();

  // step 1
  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n"
    "; cardinality constraint\n"
    "(assert (or thread_1_0 thread_1_1 thread_1_2))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not thread_1_2)))\n"
    "(assert (or (not thread_1_1) (not thread_1_2)))\n"
    "\n",
    encoder->str());

  // step 2
  reset_encoder(0, 2);

  encoder->add_thread_scheduling();

  ASSERT_EQ(
    "; thread scheduling ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n"
    "\n"
    "; store buffer flush variables - flush_<step>_<thread>\n"
    "(declare-fun flush_2_0 () Bool)\n"
    "(declare-fun flush_2_1 () Bool)\n"
    "(declare-fun flush_2_2 () Bool)\n"
    "\n"
    "; store buffer constraints\n"
    "(assert "
      "(ite sb-full_2_0 "
        "(=> (or stmt_2_0_0 stmt_2_0_1 stmt_2_0_2) (not thread_2_0)) "
        "(not flush_2_0)))\n"
    "(assert "
      "(ite sb-full_2_1 "
        "(=> (or stmt_2_1_0 stmt_2_1_1 stmt_2_1_2) (not thread_2_1)) "
        "(not flush_2_1)))\n"
    "(assert "
      "(ite sb-full_2_2 "
        "(=> (or stmt_2_2_0 stmt_2_2_1 stmt_2_2_2) (not thread_2_2)) "
        "(not flush_2_2)))\n"
    "\n"
    "; cardinality constraint\n"
    "(assert (or thread_2_0 thread_2_1 thread_2_2 flush_2_0 flush_2_1 flush_2_2))\n"
    "(assert (or (not thread_2_0) (not thread_2_1)))\n"
    "(assert (or (not thread_2_0) (not thread_2_2)))\n"
    "(assert (or (not thread_2_0) (not flush_2_0)))\n"
    "(assert (or (not thread_2_0) (not flush_2_1)))\n"
    "(assert (or (not thread_2_0) (not flush_2_2)))\n"
    "(assert (or (not thread_2_1) (not thread_2_2)))\n"
    "(assert (or (not thread_2_1) (not flush_2_0)))\n"
    "(assert (or (not thread_2_1) (not flush_2_1)))\n"
    "(assert (or (not thread_2_1) (not flush_2_2)))\n"
    "(assert (or (not thread_2_2) (not flush_2_0)))\n"
    "(assert (or (not thread_2_2) (not flush_2_1)))\n"
    "(assert (or (not thread_2_2) (not flush_2_2)))\n"
    "(assert (or (not flush_2_0) (not flush_2_1)))\n"
    "(assert (or (not flush_2_0) (not flush_2_2)))\n"
    "(assert (or (not flush_2_1) (not flush_2_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0, 2);

  verbose = false;
  encoder->add_thread_scheduling();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_2_0 () Bool)\n"
    "(declare-fun thread_2_1 () Bool)\n"
    "(declare-fun thread_2_2 () Bool)\n"
    "\n"
    "(declare-fun flush_2_0 () Bool)\n"
    "(declare-fun flush_2_1 () Bool)\n"
    "(declare-fun flush_2_2 () Bool)\n"
    "\n"
    "(assert "
      "(ite sb-full_2_0 "
        "(=> (or stmt_2_0_0 stmt_2_0_1 stmt_2_0_2) (not thread_2_0)) "
        "(not flush_2_0)))\n"
    "(assert "
      "(ite sb-full_2_1 "
        "(=> (or stmt_2_1_0 stmt_2_1_1 stmt_2_1_2) (not thread_2_1)) "
        "(not flush_2_1)))\n"
    "(assert "
      "(ite sb-full_2_2 "
        "(=> (or stmt_2_2_0 stmt_2_2_1 stmt_2_2_2) (not thread_2_2)) "
        "(not flush_2_2)))\n"
    "\n"
    "(assert (or thread_2_0 thread_2_1 thread_2_2 flush_2_0 flush_2_1 flush_2_2))\n"
    "(assert (or (not thread_2_0) (not thread_2_1)))\n"
    "(assert (or (not thread_2_0) (not thread_2_2)))\n"
    "(assert (or (not thread_2_0) (not flush_2_0)))\n"
    "(assert (or (not thread_2_0) (not flush_2_1)))\n"
    "(assert (or (not thread_2_0) (not flush_2_2)))\n"
    "(assert (or (not thread_2_1) (not thread_2_2)))\n"
    "(assert (or (not thread_2_1) (not flush_2_0)))\n"
    "(assert (or (not thread_2_1) (not flush_2_1)))\n"
    "(assert (or (not thread_2_1) (not flush_2_2)))\n"
    "(assert (or (not thread_2_2) (not flush_2_0)))\n"
    "(assert (or (not thread_2_2) (not flush_2_1)))\n"
    "(assert (or (not thread_2_2) (not flush_2_2)))\n"
    "(assert (or (not flush_2_0) (not flush_2_1)))\n"
    "(assert (or (not flush_2_0) (not flush_2_2)))\n"
    "(assert (or (not flush_2_1) (not flush_2_2)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::add_checkpoint_constraints **********************************/
TEST_F(SMTLibEncoderTest, add_checkpoint_constraints)
{
  // single checkpoint - step 2
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CHECK 1\n"));

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
    "(assert (=> (and block_2_1_2 (not check_2_1)) (not thread_2_2))) ; checkpoint 1: thread 2\n"
    "\n",
    encoder->str());

  // single checkpoint - step 3+
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
    "(assert (=> (and block_3_1_2 (not check_3_1)) (not thread_3_2))) ; checkpoint 1: thread 2\n"
    "\n",
    encoder->str());

  // two different checkpoints
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 2\n");

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
    "(assert (=> (and block_3_2_2 (not check_3_2)) (not thread_3_2))) ; checkpoint 2: thread 2\n"
    "\n",
    encoder->str());

  // two identical checkpoints
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 1\n");

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
    "(assert (=> (and block_3_2_2 (not check_3_2)) (not thread_3_2))) ; checkpoint 2: thread 2\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(assert (=> (and block_2_1_2 (not check_2_1)) (not thread_2_2)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::add_statement_execution *************************************/
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
    "(assert (= exec_1_2_2 (and stmt_1_2_2 thread_1_2)))\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(assert (= exec_1_2_0 (and stmt_1_2_0 thread_1_2)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::load ********************************************************/
TEST_F(SMTLibEncoderTest, load)
{
  Load l = Load(1);

  encoder->step = 1;

  ASSERT_EQ("(select heap_0 #x0001)", encoder->load(l));

  // indirect
  l.indirect = true;

  ASSERT_EQ("(select heap_0 (select heap_0 #x0001))", encoder->load(l));
}

/* SMTLibEncoder::encode ******************************************************/
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
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n"
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n"
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_0_0 false))\n"
    "(assert (= sb-full_0_1 false))\n"
    "(assert (= sb-full_0_2 false))\n"
    "\n"
    "; heap states - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder->str());

  // verbosity
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
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n"
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n"
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n"
    "(assert (= sb-full_0_0 false))\n"
    "(assert (= sb-full_0_1 false))\n"
    "(assert (= sb-full_0_2 false))\n"
    "\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder->str());
}
