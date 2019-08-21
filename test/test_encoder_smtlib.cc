#include "test_encoder.hh"

namespace ConcuBinE::test {

//==============================================================================
// smtlib::Encoder tests
//==============================================================================

using E = smtlib::Functional;

// smtlib::Encoder::accu_var ===================================================

TEST(smtlib_Encoder, accu_var_args)
{
  ASSERT_EQ("accu_0_1", E::accu_var(0, 1));
  ASSERT_EQ("accu_1_2", E::accu_var(1, 2));
  ASSERT_EQ("accu_2_3", E::accu_var(2, 3));
}

TEST(smtlib_Encoder, accu_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("accu_0_1", encoder.accu_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("accu_1_2", encoder.accu_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("accu_2_3", encoder.accu_var());
}

// smtlib::Encoder::mem_var ====================================================

TEST(smtlib_Encoder, mem_var_args)
{
  ASSERT_EQ("mem_0_1", E::mem_var(0, 1));
  ASSERT_EQ("mem_1_2", E::mem_var(1, 2));
  ASSERT_EQ("mem_2_3", E::mem_var(2, 3));
}

TEST(smtlib_Encoder, mem_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("mem_0_1", encoder.mem_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("mem_1_2", encoder.mem_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("mem_2_3", encoder.mem_var());
}

// smtlib::Encoder::sb_adr_var =================================================

TEST(smtlib_Encoder, sb_adr_var_args)
{
  ASSERT_EQ("sb-adr_0_1", E::sb_adr_var(0, 1));
  ASSERT_EQ("sb-adr_1_2", E::sb_adr_var(1, 2));
  ASSERT_EQ("sb-adr_2_3", E::sb_adr_var(2, 3));
}

TEST(smtlib_Encoder, sb_adr_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("sb-adr_0_1", encoder.sb_adr_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("sb-adr_1_2", encoder.sb_adr_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("sb-adr_2_3", encoder.sb_adr_var());
}

// smtlib::Encoder::sb_val_var =================================================

TEST(smtlib_Encoder, sb_val_var_args)
{
  ASSERT_EQ("sb-val_0_1", E::sb_val_var(0, 1));
  ASSERT_EQ("sb-val_1_2", E::sb_val_var(1, 2));
  ASSERT_EQ("sb-val_2_3", E::sb_val_var(2, 3));
}

TEST(smtlib_Encoder, sb_val_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("sb-val_0_1", encoder.sb_val_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("sb-val_1_2", encoder.sb_val_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("sb-val_2_3", encoder.sb_val_var());
}

// smtlib::Encoder::sb_full_var ================================================

TEST(smtlib_Encoder, sb_full_var_args)
{
  ASSERT_EQ("sb-full_0_1", E::sb_full_var(0, 1));
  ASSERT_EQ("sb-full_1_2", E::sb_full_var(1, 2));
  ASSERT_EQ("sb-full_2_3", E::sb_full_var(2, 3));
}

TEST(smtlib_Encoder, sb_full_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("sb-full_0_1", encoder.sb_full_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("sb-full_1_2", encoder.sb_full_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("sb-full_2_3", encoder.sb_full_var());
}

// smtlib::Encoder::stmt_var ===================================================

TEST(smtlib_Encoder, stmt_var_args)
{
  ASSERT_EQ("stmt_0_1_2", E::stmt_var(0, 1, 2));
  ASSERT_EQ("stmt_1_2_3", E::stmt_var(1, 2, 3));
  ASSERT_EQ("stmt_2_3_4", E::stmt_var(2, 3, 4));
}

TEST(smtlib_Encoder, stmt_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  encoder.pc = 2;
  ASSERT_EQ("stmt_0_1_2", encoder.stmt_var());

  encoder.step = 1;
  encoder.thread = 2;
  encoder.pc = 3;
  ASSERT_EQ("stmt_1_2_3", encoder.stmt_var());

  encoder.step = 2;
  encoder.thread = 3;
  encoder.pc = 4;
  ASSERT_EQ("stmt_2_3_4", encoder.stmt_var());
}

// smtlib::Encoder::block_var ==================================================

TEST(smtlib_Encoder, block_var_args)
{
  ASSERT_EQ("block_6_3_0", E::block_var(6, 3, 0));
  ASSERT_EQ("block_7_4_1", E::block_var(7, 4, 1));
  ASSERT_EQ("block_8_5_2", E::block_var(8, 5, 2));
}

// smtlib::Encoder::halt_var ===================================================

TEST(smtlib_Encoder, halt_var_args)
{
  ASSERT_EQ("halt_0_1", E::halt_var(0, 1));
  ASSERT_EQ("halt_1_2", E::halt_var(1, 2));
  ASSERT_EQ("halt_2_3", E::halt_var(2, 3));
}

TEST(smtlib_Encoder, halt_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("halt_0_1", encoder.halt_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("halt_1_2", encoder.halt_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("halt_2_3", encoder.halt_var());
}

// smtlib::Encoder::heap_var ===================================================

TEST(smtlib_Encoder, heap_var_args)
{
  ASSERT_EQ("heap_0", E::heap_var(0));
  ASSERT_EQ("heap_1", E::heap_var(1));
  ASSERT_EQ("heap_2", E::heap_var(2));
}

TEST(smtlib_Encoder, heap_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  ASSERT_EQ("heap_0", encoder.heap_var());

  encoder.step = 1;
  ASSERT_EQ("heap_1", encoder.heap_var());

  encoder.step = 2;
  ASSERT_EQ("heap_2", encoder.heap_var());
}

// smtlib::Encoder::exit_flag_var ==============================================

TEST(smtlib_Encoder, exit_var_args)
{
  ASSERT_EQ("exit_0", E::exit_flag_var(0));
  ASSERT_EQ("exit_1", E::exit_flag_var(1));
  ASSERT_EQ("exit_2", E::exit_flag_var(2));
}

TEST(smtlib_Encoder, exit_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("exit_0", encoder.exit_flag_var());

  encoder.step = 1;
  ASSERT_EQ("exit_1", encoder.exit_flag_var());

  encoder.step = 2;
  ASSERT_EQ("exit_2", encoder.exit_flag_var());
}

// smtlib::Encoder::thread_var =================================================

TEST(smtlib_Encoder, thread_var_args)
{
  ASSERT_EQ("thread_0_1", E::thread_var(0, 1));
  ASSERT_EQ("thread_1_2", E::thread_var(1, 2));
  ASSERT_EQ("thread_2_3", E::thread_var(2, 3));
}

TEST(smtlib_Encoder, thread_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("thread_0_1", encoder.thread_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("thread_1_2", encoder.thread_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("thread_2_3", encoder.thread_var());
}

// smtlib::Encoder::exec_var ===================================================

TEST(smtlib_Encoder, exec_var_args)
{
  ASSERT_EQ("exec_0_1_2", E::exec_var(0, 1, 2));
  ASSERT_EQ("exec_1_2_3", E::exec_var(1, 2, 3));
  ASSERT_EQ("exec_2_3_4", E::exec_var(2, 3, 4));
}

TEST(smtlib_Encoder, exec_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  encoder.pc = 2;
  ASSERT_EQ("exec_0_1_2", encoder.exec_var());

  encoder.step = 1;
  encoder.thread = 2;
  encoder.pc = 3;
  ASSERT_EQ("exec_1_2_3", encoder.exec_var());

  encoder.step = 2;
  encoder.thread = 3;
  encoder.pc = 4;
  ASSERT_EQ("exec_2_3_4", encoder.exec_var());
}

// smtlib::Encoder::flush_var ==================================================

TEST(smtlib_Encoder, flush_var_args)
{
  ASSERT_EQ("flush_0_1", E::flush_var(0, 1));
  ASSERT_EQ("flush_1_2", E::flush_var(1, 2));
  ASSERT_EQ("flush_2_3", E::flush_var(2, 3));
}

TEST(smtlib_Encoder, flush_var)
{
  auto encoder = create<E>();

  encoder.step = 0;
  encoder.thread = 1;
  ASSERT_EQ("flush_0_1", encoder.flush_var());

  encoder.step = 1;
  encoder.thread = 2;
  ASSERT_EQ("flush_1_2", encoder.flush_var());

  encoder.step = 2;
  encoder.thread = 3;
  ASSERT_EQ("flush_2_3", encoder.flush_var());
}

// smtlib::Encoder::check_var ==================================================

TEST(smtlib_Encoder, check_var_args)
{
  ASSERT_EQ("check_0_1", E::check_var(0, 1));
  ASSERT_EQ("check_1_2", E::check_var(1, 2));
  ASSERT_EQ("check_2_3", E::check_var(2, 3));
}

// smtlib::Encoder::assign =====================================================

TEST(smtlib_Encoder, assign)
{
  auto encoder = create<E>();

  ASSERT_EQ("(assert (= foo bar))", encoder.assign("foo", "bar"));
}

// smtlib::Encoder::load =======================================================

TEST(smtlib_Encoder, load)
{
  auto encoder = create<E>();

  encoder.step = 1;
  encoder.prev = 0;
  encoder.thread = 0;

  ASSERT_EQ(
    "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
      "sb-val_0_0 "
      "(select heap_0 #x0001))",
    encoder.load(1));

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
    encoder.load(1, true));
}

// smtlib::Encoder::declare_accu ===============================================

TEST(smtlib_Encoder, declare_accu)
{
  auto encoder = create<E>(dummy(3));

  encoder.declare_accu();

  ASSERT_EQ(
    "; accu variables - accu_<step>_<thread>\n"
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_accu();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun accu_1_0 () (_ BitVec 16))\n"
    "(declare-fun accu_1_1 () (_ BitVec 16))\n"
    "(declare-fun accu_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_mem ================================================

TEST(smtlib_Encoder, declare_mem)
{
  auto encoder = create<E>(dummy(3));

  encoder.declare_mem();

  ASSERT_EQ(
    "; mem variables - mem_<step>_<thread>\n"
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_mem();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun mem_1_0 () (_ BitVec 16))\n"
    "(declare-fun mem_1_1 () (_ BitVec 16))\n"
    "(declare-fun mem_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_sb_adr =============================================

TEST(smtlib_Encoder, declare_sb_adr)
{
  auto encoder = create<E>(dummy(3));

  encoder.declare_sb_adr();

  ASSERT_EQ(
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(declare-fun sb-adr_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_sb_adr();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-adr_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-adr_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_sb_val =============================================

TEST(smtlib_Encoder, declare_sb_val)
{
  auto encoder = create<E>(dummy(3));

  encoder.declare_sb_val();

  ASSERT_EQ(
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(declare-fun sb-val_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_sb_val();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-val_1_0 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_1 () (_ BitVec 16))\n"
    "(declare-fun sb-val_1_2 () (_ BitVec 16))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_sb_full ============================================

TEST(smtlib_Encoder, declare_sb_full)
{
  auto encoder = create<E>(dummy(3));

  encoder.declare_sb_full();

  ASSERT_EQ(
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(declare-fun sb-full_1_0 () Bool)\n"
    "(declare-fun sb-full_1_1 () Bool)\n"
    "(declare-fun sb-full_1_2 () Bool)\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_sb_full();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun sb-full_1_0 () Bool)\n"
    "(declare-fun sb-full_1_1 () Bool)\n"
    "(declare-fun sb-full_1_2 () Bool)\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_stmt ===============================================

TEST(smtlib_Encoder, declare_stmt)
{
  auto encoder = create<E>(dummy(3, 2));

  encoder.declare_stmt();

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
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_stmt();
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
    encoder.str());
}

// smtlib::Encoder::declare_block ==============================================

TEST(smtlib_Encoder, declare_block)
{
  const auto code =
    "CHECK 0\n"
    "CHECK 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.declare_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(declare-fun block_1_0_0 () Bool)\n"
    "(declare-fun block_1_0_1 () Bool)\n"
    "(declare-fun block_1_0_2 () Bool)\n"
    "(declare-fun block_1_1_0 () Bool)\n"
    "(declare-fun block_1_1_1 () Bool)\n"
    "(declare-fun block_1_1_2 () Bool)\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_block();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun block_1_0_0 () Bool)\n"
    "(declare-fun block_1_0_1 () Bool)\n"
    "(declare-fun block_1_0_2 () Bool)\n"
    "(declare-fun block_1_1_0 () Bool)\n"
    "(declare-fun block_1_1_1 () Bool)\n"
    "(declare-fun block_1_1_2 () Bool)\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, declare_block_empty)
{
  auto encoder = create<E>();

  encoder.declare_block();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::declare_halt ===============================================

TEST(smtlib_Encoder, declare_halt)
{
  auto encoder = create<E>(dummy(3));

  encoder.declare_halt();

  ASSERT_EQ(
    "; halt variables - halt_<step>_<thread>\n"
    "(declare-fun halt_1_0 () Bool)\n"
    "(declare-fun halt_1_1 () Bool)\n"
    "(declare-fun halt_1_2 () Bool)\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_halt();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun halt_1_0 () Bool)\n"
    "(declare-fun halt_1_1 () Bool)\n"
    "(declare-fun halt_1_2 () Bool)\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, declare_halt_empty)
{
  auto encoder = create<E>();

  encoder.declare_halt();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::declare_heap ===============================================

TEST(smtlib_Encoder, declare_heap)
{
  auto encoder = create<E>();

  encoder.step = 1;

  encoder.declare_heap();

  ASSERT_EQ(
    "; heap variable - heap_<step>\n"
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_heap();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun heap_1 () (Array (_ BitVec 16) (_ BitVec 16)))\n\n",
    encoder.str());
}

// smtlib::Encoder::declare_exit_flag ==========================================

TEST(smtlib_Encoder, declare_exit_flag)
{
  auto encoder = create<E>(Program::list(prog("EXIT 1")));

  encoder.declare_exit_flag();

  ASSERT_EQ(
    "; exit flag variable - exit_<step>\n"
    "(declare-fun exit_1 () Bool)\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_exit_flag();
  verbose = true;

  ASSERT_EQ("(declare-fun exit_1 () Bool)\n\n", encoder.str());
}

TEST(smtlib_Encoder, declare_exit_flag_empty)
{
  auto encoder = create<E>();

  encoder.declare_exit_flag();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::declare_exit_code ==========================================

TEST(smtlib_Encoder, declare_exit_code)
{
  auto encoder = create<E>();

  encoder.declare_exit_code();

  ASSERT_EQ(
    "; exit code variable\n"
    "(declare-fun exit-code () (_ BitVec 16))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_thread =============================================

TEST(smtlib_Encoder, declare_thread)
{
  auto encoder = create<E>(dummy(3, 3));

  encoder.declare_thread();

  ASSERT_EQ(
    "; thread activation variables - thread_<step>_<thread>\n"
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_thread();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun thread_1_0 () Bool)\n"
    "(declare-fun thread_1_1 () Bool)\n"
    "(declare-fun thread_1_2 () Bool)\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_exec ===============================================

TEST(smtlib_Encoder, declare_exec)
{
  auto encoder = create<E>(dummy(3, 2));

  encoder.declare_exec();

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
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_exec();
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
    encoder.str());
}

// smtlib::Encoder::declare_flush ==============================================

TEST(smtlib_Encoder, declare_flush)
{
  auto encoder = create<E>(dummy(3));

  encoder.declare_flush();

  ASSERT_EQ(
    "; store buffer flush variables - flush_<step>_<thread>\n"
    "(declare-fun flush_1_0 () Bool)\n"
    "(declare-fun flush_1_1 () Bool)\n"
    "(declare-fun flush_1_2 () Bool)\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_flush();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun flush_1_0 () Bool)\n"
    "(declare-fun flush_1_1 () Bool)\n"
    "(declare-fun flush_1_2 () Bool)\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::declare_check ==============================================

TEST(smtlib_Encoder, declare_check)
{
  auto programs = dummy(3);

  word_t check_id = 1;

  // 3 different checkpoint ids
  for (auto & p : *programs)
    p = prog("CHECK " + std::to_string(check_id++) + eol + p.print());

  auto encoder = create<E>(programs);

  encoder.declare_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "\n",
    encoder.str());

  // same checkpoint ids
  for (auto & p : *programs)
    p = prog("CHECK " + std::to_string(check_id) + eol + p.print());

  reset(encoder);

  encoder.declare_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.declare_check();
  verbose = true;

  ASSERT_EQ(
    "(declare-fun check_1_1 () Bool)\n"
    "(declare-fun check_1_2 () Bool)\n"
    "(declare-fun check_1_3 () Bool)\n"
    "(declare-fun check_1_4 () Bool)\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, declare_check_empty)
{
  auto encoder = create<E>();

  encoder.declare_check();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::init_accu ==================================================

TEST(smtlib_Encoder, init_accu)
{
  auto encoder = create<E>(dummy(3), mmap({}), 0);

  encoder.init_accu();

  ASSERT_EQ(
    "; accu variables - accu_<step>_<thread>\n"
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_accu();
  verbose = true;

  ASSERT_EQ(
    "(assert (= accu_0_0 #x0000))\n"
    "(assert (= accu_0_1 #x0000))\n"
    "(assert (= accu_0_2 #x0000))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::init_mem ===================================================

TEST(smtlib_Encoder, init_mem)
{
  auto encoder = create<E>(dummy(3), mmap({}), 0);

  encoder.init_mem();

  ASSERT_EQ(
    "; mem variables - mem_<step>_<thread>\n"
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_mem();
  verbose = true;

  ASSERT_EQ(
    "(assert (= mem_0_0 #x0000))\n"
    "(assert (= mem_0_1 #x0000))\n"
    "(assert (= mem_0_2 #x0000))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::init_sb_adr ================================================

TEST(smtlib_Encoder, init_sb_adr)
{
  auto encoder = create<E>(dummy(3), mmap({}), 0);

  encoder.init_sb_adr();

  ASSERT_EQ(
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_sb_adr();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-adr_0_0 #x0000))\n"
    "(assert (= sb-adr_0_1 #x0000))\n"
    "(assert (= sb-adr_0_2 #x0000))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::init_sb_val ================================================

TEST(smtlib_Encoder, init_sb_val)
{
  auto encoder = create<E>(dummy(3), mmap({}), 0);

  encoder.init_sb_val();

  ASSERT_EQ(
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_sb_val();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-val_0_0 #x0000))\n"
    "(assert (= sb-val_0_1 #x0000))\n"
    "(assert (= sb-val_0_2 #x0000))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::init_sb_full ===============================================

TEST(smtlib_Encoder, init_sb_full)
{
  auto encoder = create<E>(dummy(3), mmap({}), 0);

  encoder.init_sb_full();

  ASSERT_EQ(
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(assert (not sb-full_0_0))\n"
    "(assert (not sb-full_0_1))\n"
    "(assert (not sb-full_0_2))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_sb_full();
  verbose = true;

  ASSERT_EQ(
    "(assert (not sb-full_0_0))\n"
    "(assert (not sb-full_0_1))\n"
    "(assert (not sb-full_0_2))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::init_stmt ==================================================

TEST(smtlib_Encoder, init_stmt)
{
  auto encoder = create<E>(dummy(3, 2), mmap({}), 0);

  encoder.init_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert stmt_0_0_0)\n"
    "(assert (not stmt_0_0_1))\n"
    "(assert (not stmt_0_0_2))\n"
    "\n"
    "(assert stmt_0_1_0)\n"
    "(assert (not stmt_0_1_1))\n"
    "(assert (not stmt_0_1_2))\n"
    "\n"
    "(assert stmt_0_2_0)\n"
    "(assert (not stmt_0_2_1))\n"
    "(assert (not stmt_0_2_2))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_stmt();
  verbose = true;

  ASSERT_EQ(
    "(assert stmt_0_0_0)\n"
    "(assert (not stmt_0_0_1))\n"
    "(assert (not stmt_0_0_2))\n"
    "\n"
    "(assert stmt_0_1_0)\n"
    "(assert (not stmt_0_1_1))\n"
    "(assert (not stmt_0_1_2))\n"
    "\n"
    "(assert stmt_0_2_0)\n"
    "(assert (not stmt_0_2_1))\n"
    "(assert (not stmt_0_2_2))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::init_block =================================================

TEST(smtlib_Encoder, init_block)
{
  const auto code =
    "CHECK 0\n"
    "CHECK 1\n";

  auto encoder = create<E>(dup(prog(code), 3), mmap({}), 0);

  encoder.init_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(assert (not block_0_0_0))\n"
    "(assert (not block_0_0_1))\n"
    "(assert (not block_0_0_2))\n"
    "(assert (not block_0_1_0))\n"
    "(assert (not block_0_1_1))\n"
    "(assert (not block_0_1_2))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_block();
  verbose = true;

  ASSERT_EQ(
    "(assert (not block_0_0_0))\n"
    "(assert (not block_0_0_1))\n"
    "(assert (not block_0_0_2))\n"
    "(assert (not block_0_1_0))\n"
    "(assert (not block_0_1_1))\n"
    "(assert (not block_0_1_2))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, init_block_empty)
{
  auto encoder = create<E>();

  encoder.init_block();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::init_halt ==================================================

TEST(smtlib_Encoder, init_halt)
{
  auto encoder = create<E>(dummy(3), mmap({}), 0);

  encoder.init_halt();

  ASSERT_EQ(
    "; halt variables - halt_<step>_<thread>\n"
    "(assert (not halt_0_0))\n"
    "(assert (not halt_0_1))\n"
    "(assert (not halt_0_2))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_halt();
  verbose = true;

  ASSERT_EQ(
    "(assert (not halt_0_0))\n"
    "(assert (not halt_0_1))\n"
    "(assert (not halt_0_2))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, init_halt_empty)
{
  auto encoder = create<E>();

  encoder.init_halt();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::init_heap ==================================================

TEST(smtlib_Encoder, init_heap)
{
  auto encoder = create<E>(Program::list(), mmap({{0, 1}, {1, 1}}), 0);

  encoder.init_heap();

  ASSERT_EQ(
    "; heap variable - heap_<step>\n"
    "(assert (= (select heap_0 #x0000) #x0001))\n"
    "(assert (= (select heap_0 #x0001) #x0001))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_heap();
  verbose = true;

  ASSERT_EQ(
    "(assert (= (select heap_0 #x0000) #x0001))\n"
    "(assert (= (select heap_0 #x0001) #x0001))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, init_heap_empty)
{
  auto encoder = create<E>();

  encoder.init_heap();

  ASSERT_EQ("", encoder.formula.str());
  encoder.mmap.reset();
  encoder.init_heap();
  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::init_exit_flag =============================================

TEST(smtlib_Encoder, init_exit_flag)
{
  auto encoder = create<E>(Program::list(prog("EXIT 1")), mmap({}), 0);

  encoder.init_exit_flag();

  ASSERT_EQ(
    "; exit flag variable - exit_<step>\n"
    "(assert (not exit_0))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_exit_flag();
  verbose = true;

  ASSERT_EQ("(assert (not exit_0))\n\n", encoder.str());
}

TEST(smtlib_Encoder, init_exit_flag_empty)
{
  auto encoder = create<E>();

  encoder.init_exit_flag();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::init_states ================================================

TEST(smtlib_Encoder, init_states)
{
  auto encoder = create<E>(Program::list(prog("JMP 0")), mmap({}), 0);

  encoder.init_states();

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
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.init_states();
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
    encoder.str());
}

TEST(smtlib_Encoder, init_states_check_exit)
{
  const auto code =
    "CHECK 0\n"
    "EXIT 1\n";

  auto encoder = create<E>(Program::list(prog(code)), mmap({}), 0);

  encoder.init_states();

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
    encoder.str());
}

// smtlib::Encoder::define_exec ================================================

TEST(smtlib_Encoder, define_exec)
{
  auto encoder = create<E>(dummy(3, 2));

  encoder.define_exec();

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
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_exec();
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
    encoder.str());
}

// smtlib::Encoder::define_check ===============================================

TEST(smtlib_Encoder, define_check)
{
  // single checkpoint - initial step
  auto encoder = create<E>(dup(prog("CHECK 1"), 3), mmap(), 0);

  encoder.define_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(assert (not check_0_1))\n"
    "\n",
    encoder.str());

  // step 1
  reset(encoder, 1);

  encoder.define_check();

  ASSERT_EQ(
    "; checkpoint variables - check_<step>_<id>\n"
    "(assert (= check_1_1 (and block_1_1_0 block_1_1_1 block_1_1_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder, 0);

  verbose = false;
  encoder.define_check();
  verbose = true;

  ASSERT_EQ("(assert (not check_0_1))\n\n", encoder.str());
}

TEST(smtlib_Encoder, define_check_empty)
{
  auto encoder = create<E>();

  encoder.define_check();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::define_scheduling_constraints ==============================

TEST(smtlib_Encoder, define_scheduling_constraints)
{
  auto encoder = create<E>(dummy(2));

  encoder.define_scheduling_constraints();

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
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_scheduling_constraints();
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
    encoder.str());
}

TEST(smtlib_Encoder, define_scheduling_constraints_exit)
{
  auto encoder = create<E>(dup(prog("EXIT 1"), 2));

  encoder.define_scheduling_constraints();

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
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_scheduling_constraints();
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
    encoder.str());
}

TEST(smtlib_Encoder, define_scheduling_constraints_single_thread)
{
  auto encoder = create<E>(Program::list(prog("JMP 0")));

  encoder.define_scheduling_constraints();

  ASSERT_EQ(
    "; scheduling constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (xor thread_1_0 flush_1_0))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_scheduling_constraints();
  verbose = true;

  ASSERT_EQ("(assert (xor thread_1_0 flush_1_0))\n\n", encoder.str());
}

// smtlib::Encoder::define_store_buffer_constraints ============================

TEST(smtlib_Encoder, define_store_buffer_constraints)
{
  const auto code =
    "STORE 1\n"
    "FENCE\n"
    "CAS 1\n"
    "HALT\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_store_buffer_constraints();

  ASSERT_EQ(
    "; store buffer constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert "
      "(ite sb-full_1_0 "
        "(=> (or stmt_1_0_0 stmt_1_0_1 stmt_1_0_2 stmt_1_0_3) (not thread_1_0)) "
        "(not flush_1_0)))\n"
    "(assert "
      "(ite sb-full_1_1 "
        "(=> (or stmt_1_1_0 stmt_1_1_1 stmt_1_1_2 stmt_1_1_3) (not thread_1_1)) "
        "(not flush_1_1)))\n"
    "(assert "
      "(ite sb-full_1_2 "
        "(=> (or stmt_1_2_0 stmt_1_2_1 stmt_1_2_2 stmt_1_2_3) (not thread_1_2)) "
        "(not flush_1_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_store_buffer_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert "
      "(ite sb-full_1_0 "
        "(=> (or stmt_1_0_0 stmt_1_0_1 stmt_1_0_2 stmt_1_0_3) (not thread_1_0)) "
        "(not flush_1_0)))\n"
    "(assert "
      "(ite sb-full_1_1 "
        "(=> (or stmt_1_1_0 stmt_1_1_1 stmt_1_1_2 stmt_1_1_3) (not thread_1_1)) "
        "(not flush_1_1)))\n"
    "(assert "
      "(ite sb-full_1_2 "
        "(=> (or stmt_1_2_0 stmt_1_2_1 stmt_1_2_2 stmt_1_2_3) (not thread_1_2)) "
        "(not flush_1_2)))\n"
    "\n",
    encoder.str());
}

// smtlib::Encoder::define_checkpoint_constraints ==============================

TEST(smtlib_Encoder, define_checkpoint_constraints)
{
  auto programs = dup(prog("CHECK 1"), 3);
  auto encoder = create<E>(programs);

  encoder.define_checkpoint_constraints();

  ASSERT_EQ(
    "; checkpoint constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> (and block_1_1_0 (not check_1_1)) (not thread_1_0))) ; checkpoint 1: thread 0\n"
    "(assert (=> (and block_1_1_1 (not check_1_1)) (not thread_1_1))) ; checkpoint 1: thread 1\n"
    "(assert (=> (and block_1_1_2 (not check_1_1)) (not thread_1_2))) ; checkpoint 1: thread 2\n"
    "\n",
    encoder.str());

  // two different checkpoints
  for (auto & p : *programs)
    p = prog("CHECK 2\n" + p.print());

  reset(encoder);

  encoder.define_checkpoint_constraints();

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
    encoder.str());

  // two identical checkpoints
  for (auto & p : *programs)
    p = prog("CHECK 1\n" + p.print());

  reset(encoder);

  encoder.define_checkpoint_constraints();

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
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_checkpoint_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (=> (and block_1_1_0 (not check_1_1)) (not thread_1_0)))\n"
    "(assert (=> (and block_1_1_1 (not check_1_1)) (not thread_1_1)))\n"
    "(assert (=> (and block_1_1_2 (not check_1_1)) (not thread_1_2)))\n"
    "(assert (=> (and block_1_2_0 (not check_1_2)) (not thread_1_0)))\n"
    "(assert (=> (and block_1_2_1 (not check_1_2)) (not thread_1_1)))\n"
    "(assert (=> (and block_1_2_2 (not check_1_2)) (not thread_1_2)))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, define_checkpoint_constraints_empty)
{
  auto encoder = create<E>();

  encoder.define_checkpoint_constraints();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::define_halt_constraints ====================================

TEST(smtlib_Encoder, define_halt_constraints)
{
  auto encoder = create<E>(dummy(3));

  encoder.define_halt_constraints();

  ASSERT_EQ(
    "; halt constraints ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (=> halt_1_0 (not thread_1_0)))\n"
    "(assert (=> halt_1_1 (not thread_1_1)))\n"
    "(assert (=> halt_1_2 (not thread_1_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_halt_constraints();
  verbose = true;

  ASSERT_EQ(
    "(assert (=> halt_1_0 (not thread_1_0)))\n"
    "(assert (=> halt_1_1 (not thread_1_1)))\n"
    "(assert (=> halt_1_2 (not thread_1_2)))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Encoder, define_halt_constraints_empty)
{
  auto encoder = create<E>();

  encoder.define_halt_constraints();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Encoder::encode =====================================================

TEST(smtlib_Encoder, LOAD)
{
  auto encoder = create<E>();

  Instruction::Load load {Instruction::Type::none, 1};

  ASSERT_EQ(encoder.load(load.arg), encoder.encode(load));
}

TEST(smtlib_Encoder, LOAD_indirect)
{
  auto encoder = create<E>();

  Instruction::Load load {Instruction::Type::none, 1, true};

  ASSERT_EQ(encoder.load(load.arg, load.indirect), encoder.encode(load));
}

TEST(smtlib_Encoder, STORE)
{
  auto encoder = create<E>();

  Instruction::Store store {Instruction::Instruction::Type::none, 1};

  encoder.update = E::State::sb_adr;
  ASSERT_EQ("#x0001", encoder.encode(store));

  encoder.update = E::State::sb_val;
  ASSERT_EQ("accu_0_0", encoder.encode(store));
}

TEST(smtlib_Encoder, STORE_indirect)
{
  auto encoder = create<E>();

  Instruction::Store store {Instruction::Type::none, 1, true};

  encoder.update = E::State::sb_adr;
  ASSERT_EQ(encoder.load(store.arg), encoder.encode(store));

  encoder.update = E::State::sb_val;
  ASSERT_EQ("accu_0_0", encoder.encode(store));
}

TEST(smtlib_Encoder, ADD)
{
  auto encoder = create<E>();

  Instruction::Add add {Instruction::Type::none, 1};

  ASSERT_EQ(
    "(bvadd accu_0_0 " + encoder.load(add.arg) + ")",
    encoder.encode(add));
}

TEST(smtlib_Encoder, ADD_indirect)
{
  auto encoder = create<E>();

  Instruction::Add add {Instruction::Type::none, 1, true};

  ASSERT_EQ(
    "(bvadd accu_0_0 " + encoder.load(add.arg, add.indirect) + ")",
    encoder.encode(add));
}

TEST(smtlib_Encoder, ADDI)
{
  auto encoder = create<E>();

  Instruction::Addi addi {Instruction::Type::none, 1};

  ASSERT_EQ("(bvadd accu_0_0 #x0001)", encoder.encode(addi));
}

TEST(smtlib_Encoder, SUB)
{
  auto encoder = create<E>();

  Instruction::Sub sub {Instruction::Type::none, 1};

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder.load(sub.arg) + ")",
    encoder.encode(sub));
}

TEST(smtlib_Encoder, SUB_indirect)
{
  auto encoder = create<E>();

  Instruction::Sub sub {Instruction::Type::none, 1, true};

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder.load(sub.arg, sub.indirect) + ")",
    encoder.encode(sub));
}

TEST(smtlib_Encoder, SUBI)
{
  auto encoder = create<E>();

  Instruction::Subi subi {Instruction::Type::none, 1};

  ASSERT_EQ("(bvsub accu_0_0 #x0001)", encoder.encode(subi));
}

TEST(smtlib_Encoder, MUL)
{
  auto encoder = create<E>();

  Instruction::Mul mul {Instruction::Type::none, 1};

  ASSERT_EQ(
    "(bvmul accu_0_0 " + encoder.load(mul.arg) + ")",
    encoder.encode(mul));
}

TEST(smtlib_Encoder, MUL_indirect)
{
  auto encoder = create<E>();

  Instruction::Mul mul {Instruction::Type::none, 1, true};

  ASSERT_EQ(
    "(bvmul accu_0_0 " + encoder.load(mul.arg, mul.indirect) + ")",
    encoder.encode(mul));
}

TEST(smtlib_Encoder, MULI)
{
  auto encoder = create<E>();

  Instruction::Muli muli {Instruction::Type::none, 1};

  ASSERT_EQ("(bvmul accu_0_0 #x0001)", encoder.encode(muli));
}

TEST(smtlib_Encoder, CMP)
{
  auto encoder = create<E>();

  Instruction::Cmp cmp {Instruction::Type::none, 1};

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder.load(cmp.arg) + ")",
    encoder.encode(cmp));
}

TEST(smtlib_Encoder, CMP_indirect)
{
  auto encoder = create<E>();

  Instruction::Cmp cmp {Instruction::Type::none, 1, true};

  ASSERT_EQ(
    "(bvsub accu_0_0 " + encoder.load(cmp.arg, cmp.indirect) + ")",
    encoder.encode(cmp));
}

TEST(smtlib_Encoder, JMP)
{
  auto encoder = create<E>();

  Instruction::Jmp jmp {Instruction::Type::none, 1};

  ASSERT_TRUE(encoder.encode(jmp).empty());
}

TEST(smtlib_Encoder, JZ)
{
  auto encoder = create<E>();

  Instruction::Jz jz {Instruction::Type::none, 1};

  ASSERT_EQ("(= accu_0_0 #x0000)", encoder.encode(jz));
}

TEST(smtlib_Encoder, JNZ)
{
  auto encoder = create<E>();

  Instruction::Jnz jnz {Instruction::Type::none, 1};

  ASSERT_EQ("(not (= accu_0_0 #x0000))", encoder.encode(jnz));
}

TEST(smtlib_Encoder, JS)
{
  auto encoder = create<E>();

  Instruction::Js js {Instruction::Type::none, 1};

  ASSERT_EQ(
    "(= #b1 ((_ extract " +
      std::to_string(word_size - 1) +
      " " +
      std::to_string(word_size - 1) +
      ") " +
      "accu_0_0))",
    encoder.encode(js));
}

TEST(smtlib_Encoder, JNS)
{
  auto encoder = create<E>();

  Instruction::Jns jns {Instruction::Type::none, 1};

  ASSERT_EQ(
    "(= #b0 ((_ extract " +
      std::to_string(word_size - 1) +
      " " +
      std::to_string(word_size - 1) +
      ") " +
      "accu_0_0))",
    encoder.encode(jns));
}

TEST(smtlib_Encoder, JNZNS)
{
  auto encoder = create<E>();

  Instruction::Jnzns jnzns {Instruction::Type::none, 1};

  ASSERT_EQ(
    "(and (not (= accu_0_0 #x0000)) (= #b0 ((_ extract " +
      std::to_string(word_size - 1) +
      " " +
      std::to_string(word_size - 1) +
      ") accu_0_0)))",
    encoder.encode(jnzns));
}

TEST(smtlib_Encoder, MEM)
{
  auto encoder = create<E>();

  Instruction::Mem mem {Instruction::Type::none, 1};

  ASSERT_EQ(encoder.load(mem.arg), encoder.encode(mem));
}

TEST(smtlib_Encoder, MEM_indirect)
{
  auto encoder = create<E>();

  Instruction::Mem mem {Instruction::Type::none, 1, true};

  ASSERT_EQ(encoder.load(mem.arg, mem.indirect), encoder.encode(mem));
}

TEST(smtlib_Encoder, CAS)
{
  auto encoder = create<E>();

  Instruction::Cas cas {Instruction::Type::none, 1};

  encoder.update = E::State::accu;

  ASSERT_EQ(
    "(ite (= mem_0_0 (select heap_0 #x0001)) #x0001 #x0000)",
    encoder.encode(cas));

  encoder.update = E::State::heap;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_0 (select heap_0 #x0001)) "
      "(store heap_0 #x0001 accu_0_0) "
      "heap_0)",
    encoder.encode(cas));
}

TEST(smtlib_Encoder, CAS_indirect)
{
  auto encoder = create<E>();

  Instruction::Cas cas {Instruction::Type::none, 1, true};

  encoder.update = E::State::accu;

  ASSERT_EQ(
    "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) #x0001 #x0000)",
    encoder.encode(cas));

  encoder.update = E::State::heap;

  ASSERT_EQ(
    "(ite "
      "(= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
      "(store heap_0 (select heap_0 #x0001) accu_0_0) "
      "heap_0)",
    encoder.encode(cas));
}

TEST(smtlib_Encoder, CHECK)
{
  auto encoder = create<E>();

  Instruction::Check check {Instruction::Type::none, 1};

  ASSERT_TRUE(encoder.encode(check).empty());
}

TEST(smtlib_Encoder, EXIT)
{
  auto encoder = create<E>();

  Instruction::Exit exit {Instruction::Type::none, 1};

  ASSERT_EQ("#x0001", encoder.encode(exit));
}

} // namespace ConcuBinE::test
