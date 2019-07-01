#include "test_encoder_smtlib.hh"

using namespace std;

//==============================================================================
// SMTLib_Encoder tests
//==============================================================================

using E = SMTLib_Encoder;
using Impl = SMTLib_Encoder_Functional;

using SMTLib_Encoder_Test = Test::SMTLib_Encoder<E, Impl>;

// SMTLib_Encoder::accu_var ====================================================

TEST_F(SMTLib_Encoder_Test, accu_var_args)
{
  ASSERT_EQ("accu_0_1", encoder->accu_var(0, 1));
  ASSERT_EQ("accu_1_2", encoder->accu_var(1, 2));
  ASSERT_EQ("accu_2_3", encoder->accu_var(2, 3));
}

TEST_F(SMTLib_Encoder_Test, accu_var)
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

// SMTLib_Encoder::mem_var =====================================================

TEST_F(SMTLib_Encoder_Test, mem_var_args)
{
  ASSERT_EQ("mem_0_1", encoder->mem_var(0, 1));
  ASSERT_EQ("mem_1_2", encoder->mem_var(1, 2));
  ASSERT_EQ("mem_2_3", encoder->mem_var(2, 3));
}

TEST_F(SMTLib_Encoder_Test, mem_var)
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

// SMTLib_Encoder::sb_adr_var ==================================================

TEST_F(SMTLib_Encoder_Test, sb_adr_var_args)
{
  ASSERT_EQ("sb-adr_0_1", encoder->sb_adr_var(0, 1));
  ASSERT_EQ("sb-adr_1_2", encoder->sb_adr_var(1, 2));
  ASSERT_EQ("sb-adr_2_3", encoder->sb_adr_var(2, 3));
}

TEST_F(SMTLib_Encoder_Test, sb_adr_var)
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

// SMTLib_Encoder::sb_val_var ==================================================

TEST_F(SMTLib_Encoder_Test, sb_val_var_args)
{
  ASSERT_EQ("sb-val_0_1", encoder->sb_val_var(0, 1));
  ASSERT_EQ("sb-val_1_2", encoder->sb_val_var(1, 2));
  ASSERT_EQ("sb-val_2_3", encoder->sb_val_var(2, 3));
}

TEST_F(SMTLib_Encoder_Test, sb_val_var)
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

// SMTLib_Encoder::sb_full_var =================================================

TEST_F(SMTLib_Encoder_Test, sb_full_var_args)
{
  ASSERT_EQ("sb-full_0_1", encoder->sb_full_var(0, 1));
  ASSERT_EQ("sb-full_1_2", encoder->sb_full_var(1, 2));
  ASSERT_EQ("sb-full_2_3", encoder->sb_full_var(2, 3));
}

TEST_F(SMTLib_Encoder_Test, sb_full_var)
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

// SMTLib_Encoder::stmt_var ====================================================

TEST_F(SMTLib_Encoder_Test, stmt_var_args)
{
  ASSERT_EQ("stmt_0_1_2", encoder->stmt_var(0, 1, 2));
  ASSERT_EQ("stmt_1_2_3", encoder->stmt_var(1, 2, 3));
  ASSERT_EQ("stmt_2_3_4", encoder->stmt_var(2, 3, 4));
}

TEST_F(SMTLib_Encoder_Test, stmt_var)
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

// SMTLib_Encoder::block_var ===================================================

TEST_F(SMTLib_Encoder_Test, block_var_args)
{
  ASSERT_EQ("block_6_3_0", encoder->block_var(6, 3, 0));
  ASSERT_EQ("block_7_4_1", encoder->block_var(7, 4, 1));
  ASSERT_EQ("block_8_5_2", encoder->block_var(8, 5, 2));
}

// SMTLib_Encoder::heap_var ====================================================

TEST_F(SMTLib_Encoder_Test, heap_var_args)
{
  ASSERT_EQ("heap_0", encoder->heap_var(0));
  ASSERT_EQ("heap_1", encoder->heap_var(1));
  ASSERT_EQ("heap_2", encoder->heap_var(2));
}

TEST_F(SMTLib_Encoder_Test, heap_var)
{
  encoder->step = 0;
  ASSERT_EQ("heap_0", encoder->heap_var());

  encoder->step = 1;
  ASSERT_EQ("heap_1", encoder->heap_var());

  encoder->step = 2;
  ASSERT_EQ("heap_2", encoder->heap_var());
}

// SMTLib_Encoder::exit_flag_var ===============================================

TEST_F(SMTLib_Encoder_Test, exit_var_args)
{
  ASSERT_EQ("exit_0", encoder->exit_flag_var(0));
  ASSERT_EQ("exit_1", encoder->exit_flag_var(1));
  ASSERT_EQ("exit_2", encoder->exit_flag_var(2));
}

TEST_F(SMTLib_Encoder_Test, exit_var)
{
  encoder->step = 0;
  encoder->thread = 1;
  ASSERT_EQ("exit_0", encoder->exit_flag_var());

  encoder->step = 1;
  ASSERT_EQ("exit_1", encoder->exit_flag_var());

  encoder->step = 2;
  ASSERT_EQ("exit_2", encoder->exit_flag_var());
}

// SMTLib_Encoder::thread_var ==================================================

TEST_F(SMTLib_Encoder_Test, thread_var_args)
{
  ASSERT_EQ("thread_0_1", encoder->thread_var(0, 1));
  ASSERT_EQ("thread_1_2", encoder->thread_var(1, 2));
  ASSERT_EQ("thread_2_3", encoder->thread_var(2, 3));
}

TEST_F(SMTLib_Encoder_Test, thread_var)
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

// SMTLib_Encoder::exec_var ====================================================

TEST_F(SMTLib_Encoder_Test, exec_var_args)
{
  ASSERT_EQ("exec_0_1_2", encoder->exec_var(0, 1, 2));
  ASSERT_EQ("exec_1_2_3", encoder->exec_var(1, 2, 3));
  ASSERT_EQ("exec_2_3_4", encoder->exec_var(2, 3, 4));
}

TEST_F(SMTLib_Encoder_Test, exec_var)
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

// SMTLib_Encoder::flush_var ===================================================

TEST_F(SMTLib_Encoder_Test, flush_var_args)
{
  ASSERT_EQ("flush_0_1", encoder->flush_var(0, 1));
  ASSERT_EQ("flush_1_2", encoder->flush_var(1, 2));
  ASSERT_EQ("flush_2_3", encoder->flush_var(2, 3));
}

TEST_F(SMTLib_Encoder_Test, flush_var)
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

// SMTLib_Encoder::check_var ===================================================

TEST_F(SMTLib_Encoder_Test, check_var_args)
{
  ASSERT_EQ("check_0_1", encoder->check_var(0, 1));
  ASSERT_EQ("check_1_2", encoder->check_var(1, 2));
  ASSERT_EQ("check_2_3", encoder->check_var(2, 3));
}

// SMTLib_Encoder::assign ======================================================

TEST_F(SMTLib_Encoder_Test, assign)
{
  ASSERT_EQ("(assert (= foo bar))", encoder->assign("foo", "bar"));
}

// SMTLib_Encoder::load ========================================================

TEST_F(SMTLib_Encoder_Test, load)
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

// SMTLib_Encoder::declare_accu ================================================

TEST_F(SMTLib_Encoder_Test, declare_accu)
{
  add_dummy_programs(3);
  reset_encoder();

  encoder->declare_accu();

  ASSERT_EQ(
    "; accu variables - accu_<step>_<thread>\n"
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_accu();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_mem =================================================

TEST_F(SMTLib_Encoder_Test, declare_mem)
{
  add_dummy_programs(3);
  reset_encoder();

  encoder->declare_mem();

  ASSERT_EQ(
    "; mem variables - mem_<step>_<thread>\n"
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_mem();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_sb_adr ==============================================

TEST_F(SMTLib_Encoder_Test, declare_sb_adr)
{
  add_dummy_programs(3);
  reset_encoder();

  encoder->declare_sb_adr();

  ASSERT_EQ(
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_sb_adr();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-adr_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_sb_val ==============================================

TEST_F(SMTLib_Encoder_Test, declare_sb_val)
{
  add_dummy_programs(3);
  reset_encoder();

  encoder->declare_sb_val();

  ASSERT_EQ(
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_sb_val();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-val_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_sb_full =============================================

TEST_F(SMTLib_Encoder_Test, declare_sb_full)
{
  add_dummy_programs(3);
  reset_encoder();

  encoder->declare_sb_full();

  ASSERT_EQ(
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_1_0 () Bool)\n"
    "(declare-fun sb-full_1_1 () Bool)\n"
    "(declare-fun sb-full_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_sb_full();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-full_1_0 () Bool)\n"
    "(declare-fun sb-full_1_1 () Bool)\n"
    "(declare-fun sb-full_1_2 () Bool)\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_stmt ================================================

TEST_F(SMTLib_Encoder_Test, declare_stmt)
{
  add_dummy_programs(3, 3);
  reset_encoder();

  encoder->declare_stmt();

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

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_stmt();
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

// SMTLib_Encoder::declare_block ===============================================

TEST_F(SMTLib_Encoder_Test, declare_block)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(
      create_program(
        "CHECK 0\n"
        "CHECK 1\n"
      ));

  reset_encoder();

  encoder->declare_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_1_0_0 () Bool)\n"
    "(declare-fun block_1_0_1 () Bool)\n"
    "(declare-fun block_1_0_2 () Bool)\n"
    "(declare-fun block_1_1_0 () Bool)\n"
    "(declare-fun block_1_1_1 () Bool)\n"
    "(declare-fun block_1_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_block();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun block_1_0_0 () Bool)\n"
    "(declare-fun block_1_0_1 () Bool)\n"
    "(declare-fun block_1_0_2 () Bool)\n"
    "(declare-fun block_1_1_0 () Bool)\n"
    "(declare-fun block_1_1_1 () Bool)\n"
    "(declare-fun block_1_1_2 () Bool)\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Test, declare_block_empty)
{
  encoder->declare_block();

  ASSERT_EQ("", encoder->str());
}

// SMTLib_Encoder::declare_heap ================================================

TEST_F(SMTLib_Encoder_Test, declare_heap)
{
  encoder->step = 1;

  encoder->declare_heap();

  ASSERT_EQ(
    "; heap variable - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_heap();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder->str());
}

// SMTLib_Encoder::declare_exit_flag ===========================================

TEST_F(SMTLib_Encoder_Test, declare_exit_flag)
{
  programs.push_back(create_program("EXIT 1\n"));
  reset_encoder();

  encoder->declare_exit_flag();

  ASSERT_EQ(
    "; exit flag variable - exit_<step>\n"
    "(declare-fun exit_1 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_exit_flag();
  verbose = true;

  ASSERT_EQ("(declare-fun exit_1 () Bool)\n\n", encoder->str());
}

TEST_F(SMTLib_Encoder_Test, declare_exit_flag_empty)
{
  encoder->declare_exit_flag();

  ASSERT_EQ("", encoder->str());
}

// SMTLib_Encoder::declare_exit_code ===========================================

TEST_F(SMTLib_Encoder_Test, declare_exit_code)
{
  encoder->declare_exit_code();

  ASSERT_EQ(
    "; exit code variable\n"
    "(declare-fun exit-code () (_ BitVec 16))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_thread ==============================================

TEST_F(SMTLib_Encoder_Test, declare_thread)
{
  add_dummy_programs(3, 3);
  reset_encoder();

  encoder->declare_thread();

  ASSERT_EQ(
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_thread();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_exec ================================================

TEST_F(SMTLib_Encoder_Test, declare_exec)
{
  add_dummy_programs(3, 3);
  reset_encoder();

  encoder->declare_exec();

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

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_exec();
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

// SMTLib_Encoder::declare_flush ===============================================

TEST_F(SMTLib_Encoder_Test, declare_flush)
{
  add_dummy_programs(3);
  reset_encoder();

  encoder->declare_flush();

  ASSERT_EQ(
    "; store buffer flush variables - flush_<step>_<thread>\n"
    "(declare-fun flush_1_0 () Bool)\n"
    "(declare-fun flush_1_1 () Bool)\n"
    "(declare-fun flush_1_2 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_flush();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun flush_1_0 () Bool)\n"
    "(declare-fun flush_1_1 () Bool)\n"
    "(declare-fun flush_1_2 () Bool)\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::declare_check ===============================================

TEST_F(SMTLib_Encoder_Test, declare_check)
{
  add_dummy_programs(3);

  word_t check_id = 1;

  // 3 different checkpoint ids
  for (auto & p : programs)
    p = create_program(p.print() + "CHECK " + to_string(check_id++) + "\n");

  reset_encoder();

  encoder->declare_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "\n",
    encoder->str());

  // same checkpoint ids
  for (auto & p : programs)
    p = create_program(p.print() + "CHECK " + to_string(check_id) + "\n");

  reset_encoder();

  encoder->declare_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->declare_check();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Test, declare_check_empty)
{
  encoder->declare_check();

  ASSERT_EQ("", encoder->str());
}

// SMTLib_Encoder::init_accu ===================================================

TEST_F(SMTLib_Encoder_Test, init_accu)
{
  add_dummy_programs(3);
  reset_encoder(0);

  encoder->init_accu();

  ASSERT_EQ(
    "; accu variables - accu_<step>_<thread>\n"
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_accu();
  verbose = true;

  ASSERT_EQ(
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::init_mem ====================================================

TEST_F(SMTLib_Encoder_Test, init_mem)
{
  add_dummy_programs(3);
  reset_encoder(0);

  encoder->init_mem();

  ASSERT_EQ(
    "; mem variables - mem_<step>_<thread>\n"
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_mem();
  verbose = true;

  ASSERT_EQ(
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::init_sb_adr =================================================

TEST_F(SMTLib_Encoder_Test, init_sb_adr)
{
  add_dummy_programs(3);
  reset_encoder(0);

  encoder->init_sb_adr();

  ASSERT_EQ(
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_sb_adr();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::init_sb_val =================================================

TEST_F(SMTLib_Encoder_Test, init_sb_val)
{
  add_dummy_programs(3);
  reset_encoder(0);

  encoder->init_sb_val();

  ASSERT_EQ(
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_sb_val();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::init_sb_full ================================================

TEST_F(SMTLib_Encoder_Test, init_sb_full)
{
  add_dummy_programs(3);
  reset_encoder(0);

  encoder->init_sb_full();

  ASSERT_EQ(
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(assert (not sb-full_0_0))\n"
    "(assert (not sb-full_0_1))\n"
    "(assert (not sb-full_0_2))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_sb_full();
  verbose = true;

  ASSERT_EQ(
    "(assert (not sb-full_0_0))\n"
    "(assert (not sb-full_0_1))\n"
    "(assert (not sb-full_0_2))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::init_block ==================================================

TEST_F(SMTLib_Encoder_Test, init_block)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(
      create_program(
        "CHECK 0\n"
        "CHECK 1\n"
      ));

  reset_encoder(0);

  encoder->init_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(assert (not block_0_0_0))\n"
    "(assert (not block_0_0_1))\n"
    "(assert (not block_0_0_2))\n"
    "(assert (not block_0_1_0))\n"
    "(assert (not block_0_1_1))\n"
    "(assert (not block_0_1_2))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_block();
  verbose = true;

  ASSERT_EQ(
    "(assert (not block_0_0_0))\n"
    "(assert (not block_0_0_1))\n"
    "(assert (not block_0_0_2))\n"
    "(assert (not block_0_1_0))\n"
    "(assert (not block_0_1_1))\n"
    "(assert (not block_0_1_2))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Test, init_block_empty)
{
  encoder->init_block();

  ASSERT_EQ("", encoder->str());
}

// SMTLib_Encoder::init_exit_flag ==============================================

TEST_F(SMTLib_Encoder_Test, init_exit_flag)
{
  programs.push_back(create_program("EXIT 1\n"));
  reset_encoder(0);

  encoder->init_exit_flag();

  ASSERT_EQ(
    "; exit flag variable - exit_<step>\n"
    "(assert (not exit_0))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_exit_flag();
  verbose = true;

  ASSERT_EQ("(assert (not exit_0))\n\n", encoder->str());
}

TEST_F(SMTLib_Encoder_Test, init_exit_flag_empty)
{
  encoder->init_exit_flag();

  ASSERT_EQ("", encoder->str());
}

// SMTLib_Encoder::init_states =================================================

TEST_F(SMTLib_Encoder_Test, init_states)
{
  programs.push_back(create_program("JMP 0\n"));
  reset_encoder(0);

  encoder->init_states();

  ASSERT_EQ(
    "; state variable initializations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu variables - accu_<step>_<thread>\n"
    "(assert (= accu_0_0 #x0000))\n"
    "\n"
    "; mem variables - mem_<step>_<thread>\n"
    "(assert (= mem_0_0 #x0000))\n"
    "\n"
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "\n"
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "\n"
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(assert (not sb-full_0_0))\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert stmt_0_0_0)\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->init_states();
  verbose = true;

  ASSERT_EQ(
    "(assert (= accu_0_0 #x0000))\n"
    "\n"
    "(assert (= mem_0_0 #x0000))\n"
    "\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "\n"
    "(assert (not sb-full_0_0))\n"
    "\n"
    "(assert stmt_0_0_0)\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Test, init_states_check_exit)
{
  programs.push_back(
    create_program(
      "CHECK 0\n"
      "EXIT 1\n"
    ));

  reset_encoder(0);

  encoder->init_states();

  ASSERT_EQ(
    "; state variable initializations ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu variables - accu_<step>_<thread>\n"
    "(assert (= accu_0_0 #x0000))\n"
    "\n"
    "; mem variables - mem_<step>_<thread>\n"
    "(assert (= mem_0_0 #x0000))\n"
    "\n"
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "\n"
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "\n"
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(assert (not sb-full_0_0))\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert stmt_0_0_0)\n"
    "(assert (not stmt_0_0_1))\n"
    "\n"
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(assert (not block_0_0_0))\n"
    "\n"
    "; exit flag variable - exit_<step>\n"
    "(assert (not exit_0))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::define_exec =================================================

TEST_F(SMTLib_Encoder_Test, define_exec)
{
  add_dummy_programs(3, 3);
  reset_encoder();

  encoder->define_exec();

  ASSERT_EQ(
    "; statement execution variables - exec_<step>_<thread>_<pc>\n"
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
  reset_encoder();

  verbose = false;
  encoder->define_exec();
  verbose = true;

  ASSERT_EQ(
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
}

// SMTLib_Encoder::define_check ================================================

TEST_F(SMTLib_Encoder_Test, define_check)
{
  // single checkpoint - initial step
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CHECK 1\n"));

  reset_encoder(0);

  encoder->define_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(assert (not check_0_1))\n"
    "\n",
    encoder->str());

  // step 1
  reset_encoder();

  encoder->define_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(assert (= check_1_1 (and block_1_1_0 block_1_1_1 block_1_1_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder(0);

  verbose = false;
  encoder->define_check();
  verbose = true;

  ASSERT_EQ("(assert (not check_0_1))\n\n", encoder->str());
}

TEST_F(SMTLib_Encoder_Test, define_check_empty)
{
  encoder->define_check();

  ASSERT_EQ("", encoder->str());
}

// SMTLib_Encoder::define_scheduling_constraints ===============================

TEST_F(SMTLib_Encoder_Test, define_scheduling_constraints)
{
  add_dummy_programs(2);
  reset_encoder();

  encoder->define_scheduling_constraints();

  ASSERT_EQ(
    "; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (or thread_1_0 flush_1_0 thread_1_1 flush_1_1))\n"
    "(assert (or (not thread_1_0) (not flush_1_0)))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not flush_1_1)))\n"
    "(assert (or (not flush_1_0) (not thread_1_1)))\n"
    "(assert (or (not flush_1_0) (not flush_1_1)))\n"
    "(assert (or (not thread_1_1) (not flush_1_1)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_scheduling_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (or thread_1_0 flush_1_0 thread_1_1 flush_1_1))\n"
    "(assert (or (not thread_1_0) (not flush_1_0)))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not flush_1_1)))\n"
    "(assert (or (not flush_1_0) (not thread_1_1)))\n"
    "(assert (or (not flush_1_0) (not flush_1_1)))\n"
    "(assert (or (not thread_1_1) (not flush_1_1)))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Test, define_scheduling_constraints_exit)
{
  programs.push_back(create_program("EXIT 1"));
  programs.push_back(create_program("EXIT 1"));
  reset_encoder();

  encoder->define_scheduling_constraints();

  ASSERT_EQ(
    "; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (or thread_1_0 flush_1_0 thread_1_1 flush_1_1 exit_1))\n"
    "(assert (or (not thread_1_0) (not flush_1_0)))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not flush_1_1)))\n"
    "(assert (or (not thread_1_0) (not exit_1)))\n"
    "(assert (or (not flush_1_0) (not thread_1_1)))\n"
    "(assert (or (not flush_1_0) (not flush_1_1)))\n"
    "(assert (or (not flush_1_0) (not exit_1)))\n"
    "(assert (or (not thread_1_1) (not flush_1_1)))\n"
    "(assert (or (not thread_1_1) (not exit_1)))\n"
    "(assert (or (not flush_1_1) (not exit_1)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_scheduling_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (or thread_1_0 flush_1_0 thread_1_1 flush_1_1 exit_1))\n"
    "(assert (or (not thread_1_0) (not flush_1_0)))\n"
    "(assert (or (not thread_1_0) (not thread_1_1)))\n"
    "(assert (or (not thread_1_0) (not flush_1_1)))\n"
    "(assert (or (not thread_1_0) (not exit_1)))\n"
    "(assert (or (not flush_1_0) (not thread_1_1)))\n"
    "(assert (or (not flush_1_0) (not flush_1_1)))\n"
    "(assert (or (not flush_1_0) (not exit_1)))\n"
    "(assert (or (not thread_1_1) (not flush_1_1)))\n"
    "(assert (or (not thread_1_1) (not exit_1)))\n"
    "(assert (or (not flush_1_1) (not exit_1)))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Test, define_scheduling_constraints_single_thread)
{
  add_dummy_programs(1);
  reset_encoder();

  encoder->define_scheduling_constraints();

  ASSERT_EQ(
    "; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (xor thread_1_0 flush_1_0))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_scheduling_constraints();
  verbose = true;

  ASSERT_EQ("(assert (xor thread_1_0 flush_1_0))\n\n", encoder->str());
}

// SMTLib_Encoder::define_store_buffer_constraints =============================

TEST_F(SMTLib_Encoder_Test, define_store_buffer_constraints)
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
      "(ite sb-full_1_0 "
        "(=> (or stmt_1_0_0 stmt_1_0_1 stmt_1_0_2) (not thread_1_0)) "
        "(not flush_1_0)))\n"
    "(assert "
      "(ite sb-full_1_1 "
        "(=> (or stmt_1_1_0 stmt_1_1_1 stmt_1_1_2) (not thread_1_1)) "
        "(not flush_1_1)))\n"
    "(assert "
      "(ite sb-full_1_2 "
        "(=> (or stmt_1_2_0 stmt_1_2_1 stmt_1_2_2) (not thread_1_2)) "
        "(not flush_1_2)))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_store_buffer_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert "
      "(ite sb-full_1_0 "
        "(=> (or stmt_1_0_0 stmt_1_0_1 stmt_1_0_2) (not thread_1_0)) "
        "(not flush_1_0)))\n"
    "(assert "
      "(ite sb-full_1_1 "
        "(=> (or stmt_1_1_0 stmt_1_1_1 stmt_1_1_2) (not thread_1_1)) "
        "(not flush_1_1)))\n"
    "(assert "
      "(ite sb-full_1_2 "
        "(=> (or stmt_1_2_0 stmt_1_2_1 stmt_1_2_2) (not thread_1_2)) "
        "(not flush_1_2)))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder::define_checkpoint_contraints ================================

TEST_F(SMTLib_Encoder_Test, define_checkpoint_contraints)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CHECK 1\n"));

  reset_encoder();

  encoder->define_checkpoint_contraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (and block_1_1_0 (not check_1_1)) (not thread_1_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_1_1_1 (not check_1_1)) (not thread_1_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_1_1_2 (not check_1_1)) (not thread_1_2))) ; checkpoint 1: thread 2\n"
    "\n",
    encoder->str());

  // two different checkpoints
  for (auto & p : programs)
    p = create_program(p.print() + "CHECK 2\n");

  reset_encoder();

  encoder->define_checkpoint_contraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (and block_1_1_0 (not check_1_1)) (not thread_1_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_1_1_1 (not check_1_1)) (not thread_1_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_1_1_2 (not check_1_1)) (not thread_1_2))) ; checkpoint 1: thread 2\n"
    "(assert (=> (and block_1_2_0 (not check_1_2)) (not thread_1_0))) ; checkpoint 2: thread 0\n"
    "(assert (=> (and block_1_2_1 (not check_1_2)) (not thread_1_1))) ; checkpoint 2: thread 1\n"
    "(assert (=> (and block_1_2_2 (not check_1_2)) (not thread_1_2))) ; checkpoint 2: thread 2\n"
    "\n",
    encoder->str());

  // two identical checkpoints
  for (auto & p : programs)
    p = create_program(p.print() + "CHECK 1\n");

  reset_encoder();

  encoder->define_checkpoint_contraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (and block_1_1_0 (not check_1_1)) (not thread_1_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_1_1_1 (not check_1_1)) (not thread_1_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_1_1_2 (not check_1_1)) (not thread_1_2))) ; checkpoint 1: thread 2\n"
    "(assert (=> (and block_1_2_0 (not check_1_2)) (not thread_1_0))) ; checkpoint 2: thread 0\n"
    "(assert (=> (and block_1_2_1 (not check_1_2)) (not thread_1_1))) ; checkpoint 2: thread 1\n"
    "(assert (=> (and block_1_2_2 (not check_1_2)) (not thread_1_2))) ; checkpoint 2: thread 2\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_checkpoint_contraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (=> (and block_1_1_0 (not check_1_1)) (not thread_1_0)))\n"
    "(assert (=> (and block_1_1_1 (not check_1_1)) (not thread_1_1)))\n"
    "(assert (=> (and block_1_1_2 (not check_1_1)) (not thread_1_2)))\n"
    "(assert (=> (and block_1_2_0 (not check_1_2)) (not thread_1_0)))\n"
    "(assert (=> (and block_1_2_1 (not check_1_2)) (not thread_1_1)))\n"
    "(assert (=> (and block_1_2_2 (not check_1_2)) (not thread_1_2)))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Test, define_checkpoint_contraints_empty)
{
  encoder->define_checkpoint_contraints();

  ASSERT_EQ("", encoder->str());
}

// SMTLib_Encoder::encode ======================================================

TEST_F(SMTLib_Encoder_Test, LOAD)
{
  Instruction::Load load (1);

  ASSERT_EQ(encoder->load(load.arg), encoder->encode(load));
}

TEST_F(SMTLib_Encoder_Test, LOAD_indirect)
{
  Instruction::Load load (1, true);

  ASSERT_EQ(encoder->load(load.arg, load.indirect), encoder->encode(load));
}

TEST_F(SMTLib_Encoder_Test, STORE)
{
  Instruction::Store store (1);

  encoder->update = ::Encoder::State::sb_adr;
  ASSERT_EQ("#x0001", encoder->encode(store));

  encoder->update = ::Encoder::State::sb_val;
  ASSERT_EQ("accu_0_0", encoder->encode(store));
}

TEST_F(SMTLib_Encoder_Test, STORE_indirect)
{
  Instruction::Store store (1, true);

  encoder->update = ::Encoder::State::sb_adr;
  ASSERT_EQ(encoder->load(store.arg), encoder->encode(store));

  encoder->update = ::Encoder::State::sb_val;
  ASSERT_EQ("accu_0_0", encoder->encode(store));
}

TEST_F(SMTLib_Encoder_Test, ADD)
{
  Instruction::Add add (1);

  ASSERT_EQ(
    "(bvadd accu_0_0 " + encoder->load(add.arg) + ")",
    encoder->encode(add));
}

TEST_F(SMTLib_Encoder_Test, ADD_indirect)
{
  Instruction::Add add (1, true);

  ASSERT_EQ(
    "(bvadd accu_0_0 " + encoder->load(add.arg, add.indirect) + ")",
    encoder->encode(add));
}

TEST_F(SMTLib_Encoder_Test, ADDI)
{
  Instruction::Addi addi (1);

  ASSERT_EQ("(bvadd accu_0_0 #x0001)", encoder->encode(addi));
}

TEST_F(SMTLib_Encoder_Test, SUB)
{
  Instruction::Sub sub (1);

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder->load(sub.arg) + ")",
    encoder->encode(sub));
}

TEST_F(SMTLib_Encoder_Test, SUB_indirect)
{
  Instruction::Sub sub (1, true);

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder->load(sub.arg, sub.indirect) + ")",
    encoder->encode(sub));
}

TEST_F(SMTLib_Encoder_Test, SUBI)
{
  Instruction::Subi subi (1);

  ASSERT_EQ("(bvsub accu_0_0 #x0001)", encoder->encode(subi));
}

TEST_F(SMTLib_Encoder_Test, MUL)
{
  Instruction::Mul mul (1);

  ASSERT_EQ(
    "(bvmul accu_0_0 " + encoder->load(mul.arg) + ")",
    encoder->encode(mul));
}

TEST_F(SMTLib_Encoder_Test, MUL_indirect)
{
  Instruction::Mul mul (1, true);

  ASSERT_EQ(
    "(bvmul accu_0_0 " + encoder->load(mul.arg, mul.indirect) + ")",
    encoder->encode(mul));
}

TEST_F(SMTLib_Encoder_Test, MULI)
{
  Instruction::Muli muli (1);

  ASSERT_EQ("(bvmul accu_0_0 #x0001)", encoder->encode(muli));
}

TEST_F(SMTLib_Encoder_Test, CMP)
{
  Instruction::Cmp cmp (1);

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder->load(cmp.arg) + ")",
    encoder->encode(cmp));
}

TEST_F(SMTLib_Encoder_Test, CMP_indirect)
{
  Instruction::Cmp cmp (1, true);

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder->load(cmp.arg, cmp.indirect) + ")",
    encoder->encode(cmp));
}

TEST_F(SMTLib_Encoder_Test, JMP)
{
  Instruction::Jmp jmp (1);

  ASSERT_TRUE(encoder->encode(jmp).empty());
}

TEST_F(SMTLib_Encoder_Test, JZ)
{
  Instruction::Jz jz (1);

  ASSERT_EQ("(= accu_0_0 #x0000)", encoder->encode(jz));
}

TEST_F(SMTLib_Encoder_Test, JNZ)
{
  Instruction::Jnz jnz (1);

  ASSERT_EQ("(not (= accu_0_0 #x0000))", encoder->encode(jnz));
}

TEST_F(SMTLib_Encoder_Test, JS)
{
  Instruction::Js js (1);

  ASSERT_EQ(
    "(= #b1 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_0_0))",
    encoder->encode(js));
}

TEST_F(SMTLib_Encoder_Test, JNS)
{
  Instruction::Jns jns (1);

  ASSERT_EQ(
    "(= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") " +
      "accu_0_0))",
    encoder->encode(jns));
}

TEST_F(SMTLib_Encoder_Test, JNZNS)
{
  Instruction::Jnzns jnzns (1);

  ASSERT_EQ(
    "(and (not (= accu_0_0 #x0000)) (= #b0 ((_ extract " +
      to_string(word_size - 1) +
      " " +
      to_string(word_size - 1) +
      ") accu_0_0)))",
    encoder->encode(jnzns));
}

TEST_F(SMTLib_Encoder_Test, MEM)
{
  Instruction::Mem mem (1);

  ASSERT_EQ(encoder->load(mem.arg), encoder->encode(mem));
}

TEST_F(SMTLib_Encoder_Test, MEM_indirect)
{
  Instruction::Mem mem (1, true);

  ASSERT_EQ(encoder->load(mem.arg, mem.indirect), encoder->encode(mem));
}

TEST_F(SMTLib_Encoder_Test, CAS)
{
  Instruction::Cas cas (1);

  encoder->update = ::Encoder::State::accu;

  ASSERT_EQ(
    "(ite (= mem_0_0 (select heap_0 #x0001)) #x0001 #x0000)",
    encoder->encode(cas));

  encoder->update = ::Encoder::State::heap;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_0 (select heap_0 #x0001)) "
      "(store heap_0 #x0001 accu_0_0) "
      "heap_0)",
    encoder->encode(cas));
}

TEST_F(SMTLib_Encoder_Test, CAS_indirect)
{
  Instruction::Cas cas (1, true);

  encoder->update = ::Encoder::State::accu;

  ASSERT_EQ(
    "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) #x0001 #x0000)",
    encoder->encode(cas));

  encoder->update = ::Encoder::State::heap;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
      "(store heap_0 (select heap_0 #x0001) accu_0_0) "
      "heap_0)",
    encoder->encode(cas));
}

TEST_F(SMTLib_Encoder_Test, CHECK)
{
  Instruction::Check check (1);

  ASSERT_TRUE(encoder->encode(check).empty());
}

TEST_F(SMTLib_Encoder_Test, EXIT)
{
  Instruction::Exit exit (1);

  ASSERT_EQ("#x0001", encoder->encode(exit));
}
