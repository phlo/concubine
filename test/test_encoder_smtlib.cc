#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct SMTLibEncoderTest : public ::testing::Test
{
  Program_list      programs;
  SMTLibEncoder_ptr encoder = create_encoder();

  Program_ptr create_program (string code)
    {
      string path = "dummy.asm";
      istringstream inbuf {code};
      return make_shared<Program>(inbuf, path);
    }

  SMTLibEncoder_ptr create_encoder (const word_t bound = 0)
    {
      SMTLibEncoder_ptr e = make_shared<SMTLibEncoderFunctional>(
        make_shared<Program_list>(programs),
        bound,
        false);

      return e;
    }

  void reset_encoder (bound_t step = 0)
    {
      encoder = create_encoder(step);
      encoder->step = step;
      encoder->prev = step - 1;
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
  encoder->step = 0;
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
  encoder->step = 0;
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
  encoder->step = 0;
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
  encoder->step = 0;
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
  encoder->step = 0;
  encoder->thread = 1;
  ASSERT_EQ("sb-full_0_1", encoder->sb_full_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("sb-full_1_2", encoder->sb_full_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("sb-full_2_3", encoder->sb_full_var());
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
  encoder->step = 0;
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

/* SMTLibEncoder::block_var ***************************************************/
TEST_F(SMTLibEncoderTest, block_var_args)
{
  ASSERT_EQ("block_6_3_0", encoder->block_var(6, 3, 0));
  ASSERT_EQ("block_7_4_1", encoder->block_var(7, 4, 1));
  ASSERT_EQ("block_8_5_2", encoder->block_var(8, 5, 2));
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
  encoder->step = 0;
  ASSERT_EQ("heap_0", encoder->heap_var());

  encoder->step = 1;
  ASSERT_EQ("heap_1", encoder->heap_var());

  encoder->step = 2;
  ASSERT_EQ("heap_2", encoder->heap_var());
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
  encoder->step = 0;
  encoder->thread = 1;
  ASSERT_EQ("exit_0", encoder->exit_var());

  encoder->step = 1;
  ASSERT_EQ("exit_1", encoder->exit_var());

  encoder->step = 2;
  ASSERT_EQ("exit_2", encoder->exit_var());
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
  encoder->step = 0;
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
  encoder->step = 0;
  encoder->thread = 1;
  ASSERT_EQ("flush_0_1", encoder->flush_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("flush_1_2", encoder->flush_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("flush_2_3", encoder->flush_var());
}

/* SMTLibEncoder::check_var ***************************************************/
TEST_F(SMTLibEncoderTest, check_var_args)
{
  ASSERT_EQ("check_0_1", encoder->check_var(0, 1));
  ASSERT_EQ("check_1_2", encoder->check_var(1, 2));
  ASSERT_EQ("check_2_3", encoder->check_var(2, 3));
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
  encoder->step = 0;
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

#ifdef NIGNORE
/* SMTLibEncoder::cas_var *****************************************************/
TEST_F(SMTLibEncoderTest, cas_var_args)
{
  ASSERT_EQ("cas_0_1", encoder->cas_var(0, 1));
  ASSERT_EQ("cas_1_2", encoder->cas_var(1, 2));
  ASSERT_EQ("cas_2_3", encoder->cas_var(2, 3));
}

TEST_F(SMTLibEncoderTest, cas_var)
{
  encoder->step = 0;
  encoder->thread = 1;
  ASSERT_EQ("cas_0_1", encoder->cas_var());

  encoder->step = 1;
  encoder->thread = 2;
  ASSERT_EQ("cas_1_2", encoder->cas_var());

  encoder->step = 2;
  encoder->thread = 3;
  ASSERT_EQ("cas_2_3", encoder->cas_var());
}
#endif

/* SMTLibEncoder::assign_var **************************************************/
TEST_F(SMTLibEncoderTest, assign_var)
{
  ASSERT_EQ("(assert (= foo bar))", encoder->assign_var("foo", "bar"));
}

/* SMTLibEncoder::load ********************************************************/
TEST_F(SMTLibEncoderTest, load)
{
  encoder->step = 1;
  encoder->prev = 0;
  encoder->thread = 0;

  ASSERT_EQ(
    "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
      "sb-val_0_0 "
      "(select heap_0 #x0001))",
    encoder->load(1));

  // indirect
  ASSERT_EQ(
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
      "(select heap_0 (select heap_0 #x0001)))",
    encoder->load(1, true));
}

/* SMTLibEncoder::declare_accu ************************************************/
TEST_F(SMTLibEncoderTest, declare_accu)
{
  add_dummy_programs(3, 3);

  encoder->declare_accu();

  ASSERT_EQ(
    "; accu states - accu_<step>_<thread>\n"
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_accu();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_0_0 () (_ BitVec 16))\n"
    "(declare-fun accu_0_1 () (_ BitVec 16))\n"
    "(declare-fun accu_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_mem *************************************************/
TEST_F(SMTLibEncoderTest, declare_mem)
{
  add_dummy_programs(3, 3);

  encoder->declare_mem();

  ASSERT_EQ(
    "; mem states - mem_<step>_<thread>\n"
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_mem();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun mem_0_0 () (_ BitVec 16))\n"
    "(declare-fun mem_0_1 () (_ BitVec 16))\n"
    "(declare-fun mem_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_sb_adr **********************************************/
TEST_F(SMTLibEncoderTest, declare_sb_adr)
{
  add_dummy_programs(3, 3);

  encoder->declare_sb_adr();

  ASSERT_EQ(
    "; store buffer address states - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_sb_adr();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-adr_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_sb_val *********************************************/
TEST_F(SMTLibEncoderTest, declare_sb_val)
{
  add_dummy_programs(3, 3);

  encoder->declare_sb_val();

  ASSERT_EQ(
    "; store buffer value states - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_sb_val();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-val_0_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_0_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_sb_full *********************************************/
TEST_F(SMTLibEncoderTest, declare_sb_full)
{
  add_dummy_programs(3, 3);

  encoder->declare_sb_full();

  ASSERT_EQ(
    "; store buffer full states - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_sb_full();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-full_0_0 () Bool)\n"
    "(declare-fun sb-full_0_1 () Bool)\n"
    "(declare-fun sb-full_0_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_stmt ************************************************/
TEST_F(SMTLibEncoderTest, declare_stmt)
{
  add_dummy_programs(3, 3);

  reset_encoder();

  encoder->declare_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(declare-fun stmt_0_0_0 () Bool)\n"
    "(declare-fun stmt_0_0_1 () Bool)\n"
    "(declare-fun stmt_0_0_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_0_1_0 () Bool)\n"
    "(declare-fun stmt_0_1_1 () Bool)\n"
    "(declare-fun stmt_0_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_0_2_0 () Bool)\n"
    "(declare-fun stmt_0_2_1 () Bool)\n"
    "(declare-fun stmt_0_2_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_stmt();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun stmt_0_0_0 () Bool)\n"
    "(declare-fun stmt_0_0_1 () Bool)\n"
    "(declare-fun stmt_0_0_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_0_1_0 () Bool)\n"
    "(declare-fun stmt_0_1_1 () Bool)\n"
    "(declare-fun stmt_0_1_2 () Bool)\n"
    "\n"
    "(declare-fun stmt_0_2_0 () Bool)\n"
    "(declare-fun stmt_0_2_1 () Bool)\n"
    "(declare-fun stmt_0_2_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_block ***********************************************/
TEST_F(SMTLibEncoderTest, declare_block)
{
  add_dummy_programs(3, 3);

  // single checkpoint id
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 0\n");

  reset_encoder();

  encoder->declare_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_0_0_0 () Bool)\n"
    "(declare-fun block_0_0_1 () Bool)\n"
    "(declare-fun block_0_0_2 () Bool)\n"
    "\n",
    encoder->str());

  // two checkpoint ids
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 1\n");

  reset_encoder();

  encoder->declare_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_0_0_0 () Bool)\n"
    "(declare-fun block_0_0_1 () Bool)\n"
    "(declare-fun block_0_0_2 () Bool)\n"
    "(declare-fun block_0_1_0 () Bool)\n"
    "(declare-fun block_0_1_1 () Bool)\n"
    "(declare-fun block_0_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_block();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun block_0_0_0 () Bool)\n"
    "(declare-fun block_0_0_1 () Bool)\n"
    "(declare-fun block_0_0_2 () Bool)\n"
    "(declare-fun block_0_1_0 () Bool)\n"
    "(declare-fun block_0_1_1 () Bool)\n"
    "(declare-fun block_0_1_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_heap ************************************************/
TEST_F(SMTLibEncoderTest, declare_heap)
{
  encoder->declare_heap();

  ASSERT_EQ(
    "; heap state - heap_<step>\n"
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_heap();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun heap_0 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder->str());
}

/* SMTLibEncoder::declare_exit ************************************************/
TEST_F(SMTLibEncoderTest, declare_exit)
{
  programs.push_back(create_program("EXIT 1\n"));

  reset_encoder();

  encoder->declare_exit();

  ASSERT_EQ(
    "; exit flag - exit_<step>\n"
    "(declare-fun exit_0 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_exit();
  verbose = true;

  ASSERT_EQ("(declare-fun exit_0 () Bool)\n\n", encoder->str());
}

/* SMTLibEncoder::declare_exit_code *******************************************/
TEST_F(SMTLibEncoderTest, declare_exit_code)
{
  encoder->declare_exit_code();

  ASSERT_EQ(
    "; exit code\n"
    "(declare-fun exit-code () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_thread **********************************************/
TEST_F(SMTLibEncoderTest, declare_thread)
{
  add_dummy_programs(3, 3);

  reset_encoder();

  encoder->declare_thread();

  ASSERT_EQ(
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_0_0 () Bool)\n"
    "(declare-fun thread_0_1 () Bool)\n"
    "(declare-fun thread_0_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_thread();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_0_0 () Bool)\n"
    "(declare-fun thread_0_1 () Bool)\n"
    "(declare-fun thread_0_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_flush ***********************************************/
TEST_F(SMTLibEncoderTest, declare_flush)
{
  add_dummy_programs(3, 3);

  reset_encoder();

  encoder->declare_flush();

  ASSERT_EQ(
    "; store buffer flush variables - flush_<step>_<thread>\n"
    "(declare-fun flush_0_0 () Bool)\n"
    "(declare-fun flush_0_1 () Bool)\n"
    "(declare-fun flush_0_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_flush();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun flush_0_0 () Bool)\n"
    "(declare-fun flush_0_1 () Bool)\n"
    "(declare-fun flush_0_2 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_check ***********************************************/
TEST_F(SMTLibEncoderTest, declare_check)
{
  add_dummy_programs(3, 3);

  word_t check_id = 1;

  // 3 different checkpoint ids
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK " + to_string(check_id++) + "\n");

  reset_encoder();

  encoder->declare_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_0_1 () Bool)\n"
    "(declare-fun check_0_2 () Bool)\n"
    "(declare-fun check_0_3 () Bool)\n"
    "\n",
    encoder->str());

  // same checkpoint ids
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK " + to_string(check_id) + "\n");

  reset_encoder();

  encoder->declare_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_0_1 () Bool)\n"
    "(declare-fun check_0_2 () Bool)\n"
    "(declare-fun check_0_3 () Bool)\n"
    "(declare-fun check_0_4 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_check();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun check_0_1 () Bool)\n"
    "(declare-fun check_0_2 () Bool)\n"
    "(declare-fun check_0_3 () Bool)\n"
    "(declare-fun check_0_4 () Bool)\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::declare_exec ************************************************/
TEST_F(SMTLibEncoderTest, declare_exec)
{
  add_dummy_programs(3, 3);

  reset_encoder();

  encoder->declare_exec();

  ASSERT_EQ(
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(declare-fun exec_0_0_0 () Bool)\n"
    "(declare-fun exec_0_0_1 () Bool)\n"
    "(declare-fun exec_0_0_2 () Bool)\n"
    "\n"
    "(declare-fun exec_0_1_0 () Bool)\n"
    "(declare-fun exec_0_1_1 () Bool)\n"
    "(declare-fun exec_0_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_0_2_0 () Bool)\n"
    "(declare-fun exec_0_2_1 () Bool)\n"
    "(declare-fun exec_0_2_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_exec();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun exec_0_0_0 () Bool)\n"
    "(declare-fun exec_0_0_1 () Bool)\n"
    "(declare-fun exec_0_0_2 () Bool)\n"
    "\n"
    "(declare-fun exec_0_1_0 () Bool)\n"
    "(declare-fun exec_0_1_1 () Bool)\n"
    "(declare-fun exec_0_1_2 () Bool)\n"
    "\n"
    "(declare-fun exec_0_2_0 () Bool)\n"
    "(declare-fun exec_0_2_1 () Bool)\n"
    "(declare-fun exec_0_2_2 () Bool)\n"
    "\n",
    encoder->str());
}

#ifdef NIGNORE
/* SMTLibEncoder::declare_cas_vars ********************************************/
TEST_F(SMTLibEncoderTest, declare_cas_vars)
{
  add_dummy_programs(3, 3);

  // no CAS statement
  encoder->declare_cas_vars();

  ASSERT_EQ("", encoder->str());

  // single CAS in thread 0
  programs[0] = create_program(programs[0]->print() + "CAS 0\n");

  reset_encoder();

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_0 () Bool)\n"
    "\n",
    encoder->str());

  // 1 CAS per thread
  programs[1] = create_program(programs[1]->print() + "CAS 0\n");
  programs[2] = create_program(programs[2]->print() + "CAS 0\n");

  reset_encoder();

  encoder->declare_cas_vars();

  ASSERT_EQ(
    "; CAS condition - cas_<step>_<thread>\n"
    "(declare-fun cas_1_0 () Bool)\n"
    "(declare-fun cas_1_1 () Bool)\n"
    "(declare-fun cas_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

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
#endif

/* SMTLibEncoder::define_check ************************************************/
TEST_F(SMTLibEncoderTest, define_check)
{
  // single checkpoint - initial step
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CHECK 1\n"));

  reset_encoder();

  encoder->define_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(assert (not check_0_1))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder(1);

  encoder->define_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(assert (= check_1_1 (and block_1_1_0 block_1_1_1 block_1_1_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_check();
  verbose = true;

  ASSERT_EQ("(assert (not check_0_1))\n\n", encoder->str());
}

/* SMTLibEncoder::define_exec *************************************************/
TEST_F(SMTLibEncoderTest, define_exec)
{
  add_dummy_programs(3, 3);

  encoder->define_exec();

  ASSERT_EQ(
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
    "(assert (= exec_0_0_0 (and stmt_0_0_0 thread_0_0)))\n"
    "(assert (= exec_0_0_1 (and stmt_0_0_1 thread_0_0)))\n"
    "(assert (= exec_0_0_2 (and stmt_0_0_2 thread_0_0)))\n"
    "\n"
    "(assert (= exec_0_1_0 (and stmt_0_1_0 thread_0_1)))\n"
    "(assert (= exec_0_1_1 (and stmt_0_1_1 thread_0_1)))\n"
    "(assert (= exec_0_1_2 (and stmt_0_1_2 thread_0_1)))\n"
    "\n"
    "(assert (= exec_0_2_0 (and stmt_0_2_0 thread_0_2)))\n"
    "(assert (= exec_0_2_1 (and stmt_0_2_1 thread_0_2)))\n"
    "(assert (= exec_0_2_2 (and stmt_0_2_2 thread_0_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_exec();
  verbose = true;

  ASSERT_EQ(
    "(assert (= exec_0_0_0 (and stmt_0_0_0 thread_0_0)))\n"
    "(assert (= exec_0_0_1 (and stmt_0_0_1 thread_0_0)))\n"
    "(assert (= exec_0_0_2 (and stmt_0_0_2 thread_0_0)))\n"
    "\n"
    "(assert (= exec_0_1_0 (and stmt_0_1_0 thread_0_1)))\n"
    "(assert (= exec_0_1_1 (and stmt_0_1_1 thread_0_1)))\n"
    "(assert (= exec_0_1_2 (and stmt_0_1_2 thread_0_1)))\n"
    "\n"
    "(assert (= exec_0_2_0 (and stmt_0_2_0 thread_0_2)))\n"
    "(assert (= exec_0_2_1 (and stmt_0_2_1 thread_0_2)))\n"
    "(assert (= exec_0_2_2 (and stmt_0_2_2 thread_0_2)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::define_store_buffer_constraints *****************************/
TEST_F(SMTLibEncoderTest, define_store_buffer_constraints)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "STORE 1\n"
      "FENCE\n"
      "CAS 1\n"
    ));

  reset_encoder();

  encoder->define_store_buffer_constraints();

  ASSERT_EQ(
    "; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert "
      "(ite sb-full_0_0 "
        "(=> (or stmt_0_0_0 stmt_0_0_1 stmt_0_0_2) (not thread_0_0)) "
        "(not flush_0_0)))\n"
    "(assert "
      "(ite sb-full_0_1 "
        "(=> (or stmt_0_1_0 stmt_0_1_1 stmt_0_1_2) (not thread_0_1)) "
        "(not flush_0_1)))\n"
    "(assert "
      "(ite sb-full_0_2 "
        "(=> (or stmt_0_2_0 stmt_0_2_1 stmt_0_2_2) (not thread_0_2)) "
        "(not flush_0_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_store_buffer_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert "
      "(ite sb-full_0_0 "
        "(=> (or stmt_0_0_0 stmt_0_0_1 stmt_0_0_2) (not thread_0_0)) "
        "(not flush_0_0)))\n"
    "(assert "
      "(ite sb-full_0_1 "
        "(=> (or stmt_0_1_0 stmt_0_1_1 stmt_0_1_2) (not thread_0_1)) "
        "(not flush_0_1)))\n"
    "(assert "
      "(ite sb-full_0_2 "
        "(=> (or stmt_0_2_0 stmt_0_2_1 stmt_0_2_2) (not thread_0_2)) "
        "(not flush_0_2)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::define_checkpoint_contraints ********************************/
TEST_F(SMTLibEncoderTest, define_checkpoint_contraints)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CHECK 1\n"));

  reset_encoder();

  encoder->define_checkpoint_contraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (and block_0_1_0 (not check_0_1)) (not thread_0_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_0_1_1 (not check_0_1)) (not thread_0_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_0_1_2 (not check_0_1)) (not thread_0_2))) ; checkpoint 1: thread 2\n"
    "\n",
    encoder->str());

  // two different checkpoints
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 2\n");

  reset_encoder();

  encoder->define_checkpoint_contraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (and block_0_1_0 (not check_0_1)) (not thread_0_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_0_1_1 (not check_0_1)) (not thread_0_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_0_1_2 (not check_0_1)) (not thread_0_2))) ; checkpoint 1: thread 2\n"
    "(assert (=> (and block_0_2_0 (not check_0_2)) (not thread_0_0))) ; checkpoint 2: thread 0\n"
    "(assert (=> (and block_0_2_1 (not check_0_2)) (not thread_0_1))) ; checkpoint 2: thread 1\n"
    "(assert (=> (and block_0_2_2 (not check_0_2)) (not thread_0_2))) ; checkpoint 2: thread 2\n"
    "\n",
    encoder->str());

  // two identical checkpoints
  for (auto & p : programs)
    p = create_program(p->print() + "CHECK 1\n");

  reset_encoder();

  encoder->define_checkpoint_contraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (and block_0_1_0 (not check_0_1)) (not thread_0_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_0_1_1 (not check_0_1)) (not thread_0_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_0_1_2 (not check_0_1)) (not thread_0_2))) ; checkpoint 1: thread 2\n"
    "(assert (=> (and block_0_2_0 (not check_0_2)) (not thread_0_0))) ; checkpoint 2: thread 0\n"
    "(assert (=> (and block_0_2_1 (not check_0_2)) (not thread_0_1))) ; checkpoint 2: thread 1\n"
    "(assert (=> (and block_0_2_2 (not check_0_2)) (not thread_0_2))) ; checkpoint 2: thread 2\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_checkpoint_contraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (=> (and block_0_1_0 (not check_0_1)) (not thread_0_0)))\n"
    "(assert (=> (and block_0_1_1 (not check_0_1)) (not thread_0_1)))\n"
    "(assert (=> (and block_0_1_2 (not check_0_1)) (not thread_0_2)))\n"
    "(assert (=> (and block_0_2_0 (not check_0_2)) (not thread_0_0)))\n"
    "(assert (=> (and block_0_2_1 (not check_0_2)) (not thread_0_1)))\n"
    "(assert (=> (and block_0_2_2 (not check_0_2)) (not thread_0_2)))\n"
    "\n",
    encoder->str());
}

/* SMTLibEncoder::define_scheduling_constraints *******************************/
TEST_F(SMTLibEncoderTest, define_scheduling_constraints)
{
  programs.push_back(create_program("EXIT 1"));
  programs.push_back(create_program("EXIT 1"));

  reset_encoder();

  encoder->define_scheduling_constraints();

  ASSERT_EQ(
    "; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (or thread_0_0 flush_0_0 thread_0_1 flush_0_1 exit_0))\n"
    "(assert (or (not thread_0_0) (not flush_0_0)))\n"
    "(assert (or (not thread_0_0) (not thread_0_1)))\n"
    "(assert (or (not thread_0_0) (not flush_0_1)))\n"
    "(assert (or (not thread_0_0) (not exit_0)))\n"
    "(assert (or (not flush_0_0) (not thread_0_1)))\n"
    "(assert (or (not flush_0_0) (not flush_0_1)))\n"
    "(assert (or (not flush_0_0) (not exit_0)))\n"
    "(assert (or (not thread_0_1) (not flush_0_1)))\n"
    "(assert (or (not thread_0_1) (not exit_0)))\n"
    "(assert (or (not flush_0_1) (not exit_0)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_scheduling_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (or thread_0_0 flush_0_0 thread_0_1 flush_0_1 exit_0))\n"
    "(assert (or (not thread_0_0) (not flush_0_0)))\n"
    "(assert (or (not thread_0_0) (not thread_0_1)))\n"
    "(assert (or (not thread_0_0) (not flush_0_1)))\n"
    "(assert (or (not thread_0_0) (not exit_0)))\n"
    "(assert (or (not flush_0_0) (not thread_0_1)))\n"
    "(assert (or (not flush_0_0) (not flush_0_1)))\n"
    "(assert (or (not flush_0_0) (not exit_0)))\n"
    "(assert (or (not thread_0_1) (not flush_0_1)))\n"
    "(assert (or (not thread_0_1) (not exit_0)))\n"
    "(assert (or (not flush_0_1) (not exit_0)))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLibEncoderTest, define_scheduling_constraints_single_thread)
{
  programs.push_back(create_program("EXIT 1"));

  reset_encoder();

  encoder->define_scheduling_constraints();

  ASSERT_EQ(
    "; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (or thread_0_0 flush_0_0 exit_0))\n"
    "(assert (or (not thread_0_0) (not flush_0_0)))\n"
    "(assert (or (not thread_0_0) (not exit_0)))\n"
    "(assert (or (not flush_0_0) (not exit_0)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_scheduling_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (or thread_0_0 flush_0_0 exit_0))\n"
    "(assert (or (not thread_0_0) (not flush_0_0)))\n"
    "(assert (or (not thread_0_0) (not exit_0)))\n"
    "(assert (or (not flush_0_0) (not exit_0)))\n"
    "\n",
    encoder->str());
}
