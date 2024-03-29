/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "test_encoder.hh"

#include "encoder_smtlib_relational.hh"

namespace ConcuBinE::test {

//==============================================================================
// smtlib::Relational tests
//==============================================================================

using E = smtlib::Relational;

template <>
E init (E e)
{
  e.step = e.bound;
  e.prev = e.step - 1;

  e.thread = 0;
  e.pc = 0;
  e.state = e;

  return e;
}

// smtlib::Relational::imply ===================================================

TEST(smtlib_Relational, imply)
{
  auto encoder = create<E>();

  ASSERT_EQ("(assert (=> foo bar))\n", encoder.imply("foo", "bar"));
}

// smtlib::Relational::imply_thread_executed ===================================

TEST(smtlib_Relational, imply_thread_executed)
{
  const auto code =
    "ADDI 1\n"
    "CHECK 0\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.imply_thread_executed();

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
    encoder.formula.str());
}

// smtlib::Relational::imply_thread_not_executed ===============================

TEST(smtlib_Relational, imply_thread_not_executed)
{
  const auto code =
    "ADDI 1\n"
    "CHECK 0\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.imply_thread_not_executed();

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
    encoder.formula.str());
}

// smtlib::Relational::imply_thread_flushed ====================================

TEST(smtlib_Relational, imply_thread_flushed)
{
  auto encoder = create<E>(lst(prog(instruction_set)));

  encoder.imply_thread_flushed();

  ASSERT_EQ(
    "(assert (=> flush_0_0 "
      "(and "
        "(= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0)) "
        "(not exit_1))))\n"
    "\n",
    encoder.formula.str());
}

// smtlib::Relational::imply_machine_exited ====================================

TEST(smtlib_Relational, imply_machine_exited)
{
  auto encoder = create<E>(lst(prog(instruction_set)));

  encoder.imply_machine_exited();

  ASSERT_EQ(
    "; exited\n"
    "(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))\n"
    "\n"
    "(assert (=> (not exit_1) (= exit-code #x0000)))\n"
    "\n",
    encoder.formula.str());
}

// smtlib::Relational::define_states ===========================================

TEST(smtlib_Relational, define_states)
{
  auto encoder = create<E>(lst(prog("JMP 0")));

  encoder.define_states();

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
    "(assert (=> flush_0_0 (= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0))))\n"
    "\n"
    "; exit code\n"
    "(assert (= exit-code #x0000))\n"
    "\n",
    encoder.formula.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_states();
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
    "(assert (=> flush_0_0 (= heap_1 (store heap_0 sb-adr_0_0 sb-val_0_0))))\n"
    "\n"
    "(assert (= exit-code #x0000))\n"
    "\n",
    encoder.formula.str());
}

TEST(smtlib_Relational, define_states_check_exit)
{
  const auto code =
    "CHECK 0\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_states();

  auto expected = [] (size_t thread) {
    const auto t = std::to_string(thread);
    return
      "; thread " + t + "\n"
      "(assert (=> exec_0_" + t + "_0 "
        "(and "
          "(= accu_1_"    + t + " accu_0_"    + t + ") "
          "(= mem_1_"     + t + " mem_0_"     + t + ") "
          "(= sb-adr_1_"  + t + " sb-adr_0_"  + t + ") "
          "(= sb-val_1_"  + t + " sb-val_0_"  + t + ") "
          "(= sb-full_1_" + t + " sb-full_0_" + t + ") "
          "(and (not stmt_1_" + t + "_0) stmt_1_" + t + "_1) "
          "block_1_0_" + t + " "
          "(= heap_1 heap_0) "
          "(not exit_1))))\n"
      "\n"
      "(assert (=> exec_0_" + t + "_1 "
        "(and "
          "(= accu_1_"    + t + " accu_0_"    + t + ") "
          "(= mem_1_"     + t + " mem_0_"     + t + ") "
          "(= sb-adr_1_"  + t + " sb-adr_0_"  + t + ") "
          "(= sb-val_1_"  + t + " sb-val_0_"  + t + ") "
          "(= sb-full_1_" + t + " sb-full_0_" + t + ") "
          "(and (not stmt_1_" + t + "_0) stmt_1_" + t + "_1) "
          "(= block_1_0_" + t + " (ite check_0_0 false block_0_0_" + t + ")) "
          "(= heap_1 heap_0) "
          "exit_1 "
          "(= exit-code #x0001))))\n"
      "\n"
      "(assert (=> (not thread_0_" + t + ") "
        "(and "
          "(= accu_1_"    + t + " accu_0_"    + t + ") "
          "(= mem_1_"     + t + " mem_0_"     + t + ") "
          "(= sb-adr_1_"  + t + " sb-adr_0_"  + t + ") "
          "(= sb-val_1_"  + t + " sb-val_0_"  + t + ") "
          "(= sb-full_1_" + t + " (ite flush_0_" + t + " false sb-full_0_" + t + ")) "
          "(and "
            "(= stmt_1_" + t + "_0 stmt_0_" + t + "_0) "
            "(= stmt_1_" + t + "_1 stmt_0_" + t + "_1)) "
          "(= block_1_0_" + t + " (ite check_0_0 false block_0_0_" + t + ")))))\n"
      "\n"
      "(assert (=> flush_0_" + t + " "
        "(and "
          "(= heap_1 (store heap_0 sb-adr_0_" + t + " sb-val_0_" + t + ")) "
          "(not exit_1))))\n";
  };

  ASSERT_EQ(
    "; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    + expected(0) +
    "\n"
    + expected(1) +
    "\n"
    + expected(2) +
    "\n"
    "; exited\n"
    "(assert (=> exit_0 (and (= heap_1 heap_0) exit_1)))\n"
    "\n"
    "(assert (=> (not exit_1) (= exit-code #x0000)))\n"
    "\n",
    encoder.formula.str());
}

// smtlib::Relational::encode ==================================================

TEST(smtlib_Relational, encode_check) { encode_check<E>(); }
TEST(smtlib_Relational, encode_cas) { encode_cas<E>(); }
TEST(smtlib_Relational, encode_indirect) { encode_indirect<E>(); }
TEST(smtlib_Relational, encode_halt) { encode_halt<E>(); }

TEST(smtlib_Relational, encode_demo) { encode_demo<E>(); }

TEST(smtlib_Relational, encode_litmus_intel_1) { encode_litmus_intel_1<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_2) { encode_litmus_intel_2<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_3) { encode_litmus_intel_3<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_4) { encode_litmus_intel_4<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_5) { encode_litmus_intel_5<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_6) { encode_litmus_intel_6<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_7) { encode_litmus_intel_7<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_8) { encode_litmus_intel_8<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_9) { encode_litmus_intel_9<E>(); }
TEST(smtlib_Relational, encode_litmus_intel_10) { encode_litmus_intel_10<E>(); }

TEST(smtlib_Relational, encode_litmus_amd_1) { encode_litmus_amd_1<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_2) { encode_litmus_amd_2<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_3) { encode_litmus_amd_3<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_4) { encode_litmus_amd_4<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_5) { encode_litmus_amd_5<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_6) { encode_litmus_amd_6<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_7) { encode_litmus_amd_7<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_8) { encode_litmus_amd_8<E>(); }
TEST(smtlib_Relational, encode_litmus_amd_9) { encode_litmus_amd_9<E>(); }

TEST(smtlib_Relational, LOAD)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  Instruction::Load load {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(load));
}

TEST(smtlib_Relational, LOAD_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  Instruction::Load l {Instruction::Type::none, 1, true};

  const auto load = encoder.load(l.arg, l.indirect);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 " + load + ") "
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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(l));
}

TEST(smtlib_Relational, STORE)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 1;

  Instruction::Store store {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(store));
}

TEST(smtlib_Relational, STORE_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 1;

  Instruction::Store store {Instruction::Type::none, 1, true};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(store));
}

TEST(smtlib_Relational, ADD)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 2;

  Instruction::Add add {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(add));
}

TEST(smtlib_Relational, ADD_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 2;

  Instruction::Add add {Instruction::Type::none, 1, true};

  const auto load = encoder.load(add.arg, add.indirect);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvadd accu_0_0 " + load + ")) "
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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(add));
}

TEST(smtlib_Relational, ADDI)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 3;

  Instruction::Addi addi {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(addi));
}

TEST(smtlib_Relational, SUB)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 4;

  Instruction::Sub sub {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(sub));
}

TEST(smtlib_Relational, SUB_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 4;

  Instruction::Sub sub {Instruction::Type::none, 1, true};

  const auto load = encoder.load(sub.arg, sub.indirect);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvsub accu_0_0 " + load + ")) "
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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(sub));
}

TEST(smtlib_Relational, SUBI)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 5;

  Instruction::Subi subi {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(subi));
}

TEST(smtlib_Relational, MUL)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 4;

  Instruction::Mul mul {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(mul));
}

TEST(smtlib_Relational, MUL_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 4;

  Instruction::Mul mul {Instruction::Type::none, 1, true};

  const auto load = encoder.load(mul.arg, mul.indirect);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvmul accu_0_0 " + load + ")) "
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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(mul));
}

TEST(smtlib_Relational, MULI)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 5;

  Instruction::Muli muli {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(muli));
}

TEST(smtlib_Relational, CMP)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 8;

  Instruction::Cmp cmp {Instruction::Type::none, 1};

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
        "(not stmt_1_0_7) "
        "(not stmt_1_0_8) "
        "stmt_1_0_9 "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(cmp));
}

TEST(smtlib_Relational, CMP_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 8;

  Instruction::Cmp cmp {Instruction::Type::none, 1, true};

  const auto load = encoder.load(cmp.arg, cmp.indirect);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 (bvsub accu_0_0 " + load + ")) "
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
        "stmt_1_0_9 "
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(cmp));
}

TEST(smtlib_Relational, JMP)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 9;

  Instruction::Jmp jmp {Instruction::Type::none, 10};

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
        "stmt_1_0_10 "
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(jmp));
}

TEST(smtlib_Relational, JZ)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 10;

  Instruction::Jz jz {Instruction::Type::none, 1};

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
        "(not stmt_1_0_9) "
        "(not stmt_1_0_10) "
        "(ite (= accu_0_0 #x0000) "
          "(not stmt_1_0_11) "
          "stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(jz));
}

TEST(smtlib_Relational, JNZ)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 11;

  Instruction::Jnz jnz {Instruction::Type::none, 1};

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
        "(not stmt_1_0_10) "
        "(not stmt_1_0_11) "
        "(ite (not (= accu_0_0 #x0000)) "
          "(not stmt_1_0_12) "
          "stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(jnz));
}

TEST(smtlib_Relational, JS)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 12;

  Instruction::Js js {Instruction::Type::none, 1};

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
        "(not stmt_1_0_11) "
        "(not stmt_1_0_12) "
        "(ite (= #b1 ((_ extract 15 15) accu_0_0)) "
          "(not stmt_1_0_13) "
          "stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(js));
}

TEST(smtlib_Relational, JNS)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 13;

  Instruction::Jns jns {Instruction::Type::none, 1};

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
        "(not stmt_1_0_12) "
        "(not stmt_1_0_13) "
        "(ite (= #b0 ((_ extract 15 15) accu_0_0)) "
          "(not stmt_1_0_14) "
          "stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(jns));
}

TEST(smtlib_Relational, JNZNS)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 14;

  Instruction::Jnzns jnzns {Instruction::Type::none, 1};

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
        "(not stmt_1_0_13) "
        "(not stmt_1_0_14) "
        "(ite "
          "(and "
            "(not (= accu_0_0 #x0000)) "
            "(= #b0 ((_ extract 15 15) accu_0_0))) "
          "(not stmt_1_0_15) "
          "stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(jnzns));
}

TEST(smtlib_Relational, MEM)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 15;

  Instruction::Mem mem {Instruction::Type::none, 1};

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
        "(not stmt_1_0_14) "
        "(not stmt_1_0_15) "
        "stmt_1_0_16 "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(mem));
}

TEST(smtlib_Relational, MEM_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 15;

  Instruction::Mem mem {Instruction::Type::none, 1, true};

  const auto load = encoder.load(mem.arg, mem.indirect);

  ASSERT_EQ(
    "(and "
      "(= accu_1_0 " + load + ") "
      "(= mem_1_0 " + load + ") "
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
        "stmt_1_0_16 "
        "(not stmt_1_0_17) "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(mem));
}

TEST(smtlib_Relational, CAS)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 16;

  Instruction::Cas cas {Instruction::Type::none, 1};

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
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "stmt_1_0_17 "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 "
        "(ite (= mem_0_0 (select heap_0 #x0001)) "
          "(store heap_0 #x0001 accu_0_0) "
          "heap_0)) "
      "(not exit_1))",
    encoder.encode(cas));
}

TEST(smtlib_Relational, CAS_indirect)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 16;

  Instruction::Cas cas {Instruction::Type::none, 1, true};

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
        "(not stmt_1_0_15) "
        "(not stmt_1_0_16) "
        "stmt_1_0_17 "
        "(not stmt_1_0_18)) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 "
        "(ite (= mem_0_0 (select heap_0 (select heap_0 #x0001))) "
          "(store heap_0 (select heap_0 #x0001) accu_0_0) "
          "heap_0)) "
      "(not exit_1))",
    encoder.encode(cas));
}

TEST(smtlib_Relational, CHECK)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 17;

  Instruction::Check check {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "stmt_1_0_18) "
      "block_1_1_0 "
      "(= heap_1 heap_0) "
      "(not exit_1))",
    encoder.encode(check));
}

TEST(smtlib_Relational, EXIT)
{
  auto encoder = create<E>(dup(prog(instruction_set), 2));

  encoder.pc = 18;

  Instruction::Exit exit {Instruction::Type::none, 1};

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
        "(not stmt_1_0_16) "
        "(not stmt_1_0_17) "
        "stmt_1_0_18) "
      "(= block_1_1_0 (ite check_0_1 false block_0_1_0)) "
      "(= heap_1 heap_0) "
      "exit_1 "
      "(= exit-code #x0001))",
    encoder.encode(exit));
}

} // namespace ConcuBinE::test
