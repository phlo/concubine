#include "test_encoder_smtlib.hh"

using namespace std;

//==============================================================================
// SMTLib_Encoder_Relational tests
//==============================================================================

using E = SMTLib_Encoder_Relational;

struct SMTLib_Encoder_Relational_Test : Test::SMTLib_Encoder<E>
{
  virtual std::unique_ptr<E> init_encoder (std::unique_ptr<E> e)
    {
      e->step = e->bound;
      e->prev = e->step - 1;

      e->thread = 0;
      e->pc = 0;
      e->state = *e;

      return e;
    }
};

// SMTLib_Encoder_Relational::imply ============================================

TEST_F(SMTLib_Encoder_Relational_Test, imply)
{
  ASSERT_EQ("(assert (=> foo bar))\n", encoder->imply("foo", "bar"));
}

// SMTLib_Encoder_Relational::imply_thread_executed ============================

TEST_F(SMTLib_Encoder_Relational_Test, imply_thread_executed)
{
  programs.push_back(
    create_program(
      "ADDI 1\n"
      "CHECK 0\n"
      "EXIT 1\n"));

  reset_encoder();

  encoder->imply_thread_executed();

  ASSERT_EQ(
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 (bvadd accu_0_0 #x0001)) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and "
          "(not stmt_1_0_0) "
          "stmt_1_0_1 "
          "(not stmt_1_0_2)) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)) "
        "(= heap_1 heap_0) "
        "(not exit_1))))\n"
    "\n"
    "(assert (=> exec_0_0_1 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and "
          "(not stmt_1_0_0) "
          "(not stmt_1_0_1) "
          "stmt_1_0_2) "
        "block_1_0_0 "
        "(= heap_1 heap_0) "
        "(not exit_1))))\n"
    "\n"
    "(assert (=> exec_0_0_2 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and "
          "(not stmt_1_0_0) "
          "(not stmt_1_0_1) "
          "stmt_1_0_2) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)) "
        "(= heap_1 heap_0) "
        "exit_1 "
        "(= exit-code #x0001))))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder_Relational::imply_thread_not_executed ========================

TEST_F(SMTLib_Encoder_Relational_Test, imply_thread_not_executed)
{
  programs.push_back(
    create_program(
      "ADDI 1\n"
      "CHECK 0\n"
      "EXIT 1\n"));

  reset_encoder();

  encoder->imply_thread_not_executed();

  ASSERT_EQ(
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(and "
          "(= stmt_1_0_0 stmt_0_0_0) "
          "(= stmt_1_0_1 stmt_0_0_1) "
          "(= stmt_1_0_2 stmt_0_0_2)) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)))))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder_Relational::imply_thread_flushed =============================

TEST_F(SMTLib_Encoder_Relational_Test, imply_thread_flushed)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->imply_thread_flushed();

  ASSERT_EQ(
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)) "
        "(not exit_1))))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder_Relational::imply_machine_exited =============================

TEST_F(SMTLib_Encoder_Relational_Test, imply_machine_exited)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->imply_machine_exited();

  ASSERT_EQ(
    "; exited\n"
    "(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))\n"
    "\n"
    "(assert (=> (not exit_1) (= exit-code #x0000)))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder_Relational::define_states ====================================

TEST_F(SMTLib_Encoder_Relational_Test, define_states)
{
  programs.push_back(create_program("JMP 0\n"));
  reset_encoder();

  encoder->define_states();

  ASSERT_EQ(
    "; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread 0\n"
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "stmt_1_0_0 "
        "(= heap_1 heap_0))))\n"
    "\n"
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(= stmt_1_0_0 stmt_0_0_0))))\n"
    "\n"
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)))))\n"
    "\n",
    encoder->str());

  // verbosity
  reset_encoder();

  verbose = false;
  encoder->define_states();
  verbose = true;

  ASSERT_EQ(
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "stmt_1_0_0 "
        "(= heap_1 heap_0))))\n"
    "\n"
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(= stmt_1_0_0 stmt_0_0_0))))\n"
    "\n"
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)))))\n"
    "\n",
    encoder->str());
}

TEST_F(SMTLib_Encoder_Relational_Test, define_states_check_exit)
{
  programs.push_back(
    create_program(
      "CHECK 0\n"
      "EXIT 1\n"));

  reset_encoder();

  encoder->define_states();

  ASSERT_EQ(
    "; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; thread 0\n"
    "(assert (=> exec_0_0_0 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and (not stmt_1_0_0) stmt_1_0_1) "
        "block_1_0_0 "
        "(= heap_1 heap_0) "
        "(not exit_1))))\n"
    "\n"
    "(assert (=> exec_0_0_1 "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 sb-full_0_0) "
        "(and (not stmt_1_0_0) stmt_1_0_1) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)) "
        "(= heap_1 heap_0) "
        "exit_1 "
        "(= exit-code #x0001))))\n"
    "\n"
    "(assert (=> (not thread_0_0) "
      "(and "
        "(= accu_1_0 accu_0_0) "
        "(= mem_1_0 mem_0_0) "
        "(= sb-adr_1_0 sb-adr_0_0) "
        "(= sb-val_1_0 sb-val_0_0) "
        "(= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)) "
        "(and (= stmt_1_0_0 stmt_0_0_0) (= stmt_1_0_1 stmt_0_0_1)) "
        "(= block_1_0_0 (ite check_0_0 false block_0_0_0)))))\n"
    "\n"
    "(assert (=> flush_0_0 "
      "(and "
        "(not sb-full_1_0) "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)) "
        "(not exit_1))))\n"
    "\n"
    "; exited\n"
    "(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))\n"
    "\n"
    "(assert (=> (not exit_1) (= exit-code #x0000)))\n"
    "\n",
    encoder->str());
}

// SMTLib_Encoder_Relational::encode ===========================================

TEST_F(SMTLib_Encoder_Relational_Test, encode_check)
{
  /* concurrent increment using CHECK */
  encode(
    {"increment.check.thread.0.asm", "increment.check.thread.n.asm"},
    "increment.check.relational.t2.k16.smt2",
    16);
}

TEST_F(SMTLib_Encoder_Relational_Test, encode_cas)
{
  /* concurrent increment using CAS */
  encode(
    {"increment.cas.asm", "increment.cas.asm"},
    "increment.cas.relational.t2.k16.smt2",
    16);
}

TEST_F(SMTLib_Encoder_Relational_Test, LOAD)
{
  add_instruction_set(1);
  reset_encoder();

  Instruction::Load load (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "stmt_1_0_1 "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(load));
}

TEST_F(SMTLib_Encoder_Relational_Test, LOAD_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  Instruction::Load load (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
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
          "(select heap_0 (select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "stmt_1_0_1 "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(load));
}

TEST_F(SMTLib_Encoder_Relational_Test, STORE)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 1;

  Instruction::Store store (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 #x0001) "
      "(= sb-val_1_0 accu_0_0) "
      "sb-full_1_0 "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "stmt_1_0_2 "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(store));
}

TEST_F(SMTLib_Encoder_Relational_Test, STORE_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 1;

  Instruction::Store store (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
        "sb-val_0_0 "
        "(select heap_0 #x0001))) "
      "(= sb-val_1_0 accu_0_0) "
      "sb-full_1_0 "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "stmt_1_0_2 "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(store));
}

TEST_F(SMTLib_Encoder_Relational_Test, ADD)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 2;

  Instruction::Add add (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvadd "
          "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "stmt_1_0_3 "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(add));
}

TEST_F(SMTLib_Encoder_Relational_Test, ADD_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 2;

  Instruction::Add add (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvadd "
          "accu_0_0 "
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
            "(select heap_0 (select heap_0 #x0001))))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "stmt_1_0_3 "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(add));
}

TEST_F(SMTLib_Encoder_Relational_Test, ADDI)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 3;

  Instruction::Addi addi (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvadd accu_0_0 #x0001)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "stmt_1_0_4 "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(addi));
}

TEST_F(SMTLib_Encoder_Relational_Test, SUB)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 4;

  Instruction::Sub sub (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "stmt_1_0_5 "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(sub));
}

TEST_F(SMTLib_Encoder_Relational_Test, SUB_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 4;

  Instruction::Sub sub (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
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
            "(select heap_0 (select heap_0 #x0001))))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "stmt_1_0_5 "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(sub));
}

TEST_F(SMTLib_Encoder_Relational_Test, SUBI)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 5;

  Instruction::Subi subi (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvsub accu_0_0 #x0001)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "stmt_1_0_6 "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(subi));
}

TEST_F(SMTLib_Encoder_Relational_Test, MUL)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 4;

  Instruction::Mul mul (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvmul "
          "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "stmt_1_0_5 "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(mul));
}

TEST_F(SMTLib_Encoder_Relational_Test, MUL_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 4;

  Instruction::Mul mul (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvmul "
          "accu_0_0 "
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
            "(select heap_0 (select heap_0 #x0001))))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "stmt_1_0_5 "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(mul));
}

TEST_F(SMTLib_Encoder_Relational_Test, MULI)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 5;

  Instruction::Muli muli (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvmul accu_0_0 #x0001)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "stmt_1_0_6 "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(muli));
}

TEST_F(SMTLib_Encoder_Relational_Test, CMP)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 6;

  Instruction::Cmp cmp (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001)))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "stmt_1_0_7 "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(cmp));
}

TEST_F(SMTLib_Encoder_Relational_Test, CMP_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 6;

  Instruction::Cmp cmp (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(bvsub "
          "accu_0_0 "
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
            "(select heap_0 (select heap_0 #x0001))))) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "stmt_1_0_7 "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(cmp));
}

TEST_F(SMTLib_Encoder_Relational_Test, JMP)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 7;

  Instruction::Jmp jmp (8);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "stmt_1_0_8 "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jmp));
}

TEST_F(SMTLib_Encoder_Relational_Test, JZ)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 8;

  Instruction::Jz jz (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (= accu_0_0 #x0000) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(ite (= accu_0_0 #x0000) "
          "(not stmt_1_0_9) "
          "stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jz));
}

TEST_F(SMTLib_Encoder_Relational_Test, JNZ)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 9;

  Instruction::Jnz jnz (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (not (= accu_0_0 #x0000)) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(ite (not (= accu_0_0 #x0000)) "
          "(not stmt_1_0_10) "
          "stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jnz));
}

TEST_F(SMTLib_Encoder_Relational_Test, JS)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 10;

  Instruction::Js js (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (= #b1 ((_ extract 15 15) accu_0_0)) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(ite (= #b1 ((_ extract 15 15) accu_0_0)) "
          "(not stmt_1_0_11) "
          "stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(js));
}

TEST_F(SMTLib_Encoder_Relational_Test, JNS)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 11;

  Instruction::Jns jns (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite (= #b0 ((_ extract 15 15) accu_0_0)) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(ite (= #b0 ((_ extract 15 15) accu_0_0)) "
          "(not stmt_1_0_12) "
          "stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jns));
}

TEST_F(SMTLib_Encoder_Relational_Test, JNZNS)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 12;

  Instruction::Jnzns jnzns (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(ite "
          "(and "
            "(not (= accu_0_0 #x0000)) "
            "(= #b0 ((_ extract 15 15) accu_0_0))) "
          "stmt_1_0_1 "
          "(not stmt_1_0_1)) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(ite "
          "(and "
            "(not (= accu_0_0 #x0000)) "
            "(= #b0 ((_ extract 15 15) accu_0_0))) "
          "(not stmt_1_0_13) "
          "stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(jnzns));
}

TEST_F(SMTLib_Encoder_Relational_Test, MEM)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 13;

  Instruction::Mem mem (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001))) "
      "(= mem_1_0 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001))) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "stmt_1_0_14 "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(mem));
}

TEST_F(SMTLib_Encoder_Relational_Test, MEM_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 13;

  Instruction::Mem mem (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
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
          "(select heap_0 (select heap_0 #x0001)))) "
      "(= mem_1_0 "
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
          "(select heap_0 (select heap_0 #x0001)))) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "stmt_1_0_14 "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(mem));
}

TEST_F(SMTLib_Encoder_Relational_Test, CAS)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 14;

  Instruction::Cas cas (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (= mem_0_0 (select heap_0 #x0001)) "
          "#x0001 "
          "#x0000)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "stmt_1_0_15 "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 "
        "(ite (= mem_0_0 (select heap_0 #x0001)) "
          "(store heap_0 #x0001 accu_0_0) "
          "heap_0)) "
      "(not exit_1))",
    encoder->encode(cas));
}

TEST_F(SMTLib_Encoder_Relational_Test, CAS_indirect)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 14;

  Instruction::Cas cas (1, true);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 "
        "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
          "#x0001 "
          "#x0000)) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "stmt_1_0_15 "
        "(not stmt_1_0_16)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 "
        "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
          "(store heap_0 (select heap_0 #x0001) accu_0_0) "
          "heap_0)) "
      "(not exit_1))",
    encoder->encode(cas));
}

TEST_F(SMTLib_Encoder_Relational_Test, CHECK)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 15;

  Instruction::Check check (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "stmt_1_0_16) "
      "block_1_1_0 "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder->encode(check));
}

TEST_F(SMTLib_Encoder_Relational_Test, HALT)
{
  // TODO
}

TEST_F(SMTLib_Encoder_Relational_Test, EXIT)
{
  add_instruction_set(1);
  reset_encoder();

  encoder->pc = 16;

  Instruction::Exit exit (1);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 accu_0_0) "
      "(= mem_1_0 mem_0_0) "
      "(= sb-adr_1_0 sb-adr_0_0) "
      "(= sb-val_1_0 sb-val_0_0) "
      "(= sb-full_1_0 sb-full_0_0) "
      "(and "
        "(not stmt_1_0_0) "
        "(not stmt_1_0_1) "
        "(not stmt_1_0_2) "
        "(not stmt_1_0_3) "
        "(not stmt_1_0_4) "
        "(not stmt_1_0_5) "
        "(not stmt_1_0_6) "
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "stmt_1_0_16) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "exit_1 "
      "(= exit-code #x0001))",
    encoder->encode(exit));
}
