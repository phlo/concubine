#include "test_encoder.hh"

namespace ConcuBinE::test {

//==============================================================================
// smtlib::Functional tests
//==============================================================================

using E = smtlib::Functional;

template <>
E init (E e)
{
  e.step = e.bound;
  e.prev = e.bound - 1;
  return e;
}

// smtlib::Functional::define_accu =============================================

TEST(smtlib_Functional, define_accu)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  encoder.define_accu();

  ASSERT_EQ(
    "; accu variables - accu_<step>_<thread>\n"
    "(assert (= accu_1_0 "
      "(ite exec_0_0_0 " // LOAD
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001)) "
        "(ite exec_0_0_2 " // ADD
          "(bvadd "
            "accu_0_0 "
            "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
              "sb-val_0_0 "
              "(select heap_0 #x0001))) "
          "(ite exec_0_0_3 " // ADDI
            "(bvadd accu_0_0 #x0001) "
            "(ite exec_0_0_4 " // SUB
              "(bvsub "
                "accu_0_0 "
                "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
                  "sb-val_0_0 "
                  "(select heap_0 #x0001))) "
              "(ite exec_0_0_5 " // SUBI
                "(bvsub accu_0_0 #x0001) "
                "(ite exec_0_0_6 " // MUL
                  "(bvmul "
                    "accu_0_0 "
                    "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
                      "sb-val_0_0 "
                      "(select heap_0 #x0001))) "
                  "(ite exec_0_0_7 " // MULI
                    "(bvmul accu_0_0 #x0001) "
                    "(ite exec_0_0_8 " // CMP
                      "(bvsub "
                        "accu_0_0 "
                        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
                          "sb-val_0_0 "
                          "(select heap_0 #x0001))) "
                      "(ite exec_0_0_15 " // MEM
                        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
                          "sb-val_0_0 "
                          "(select heap_0 #x0001)) "
                        "(ite exec_0_0_16 " // CAS
                          "(ite (= mem_0_0 (select heap_0 #x0001)) "
                            "#x0001 "
                            "#x0000) "
                          "accu_0_0))))))))))))\n"
    "(assert (= accu_1_1 "
      "(ite exec_0_1_0 " // LOAD
        "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
          "sb-val_0_1 "
          "(select heap_0 #x0001)) "
        "(ite exec_0_1_2 " // ADD
          "(bvadd "
            "accu_0_1 "
            "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
              "sb-val_0_1 "
              "(select heap_0 #x0001))) "
          "(ite exec_0_1_3 " // ADDI
            "(bvadd accu_0_1 #x0001) "
            "(ite exec_0_1_4 " // SUB
              "(bvsub "
                "accu_0_1 "
                "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
                  "sb-val_0_1 "
                  "(select heap_0 #x0001))) "
              "(ite exec_0_1_5 " // SUBI
                "(bvsub accu_0_1 #x0001) "
                "(ite exec_0_1_6 " // MUL
                  "(bvmul "
                    "accu_0_1 "
                    "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
                      "sb-val_0_1 "
                      "(select heap_0 #x0001))) "
                  "(ite exec_0_1_7 " // MULI
                    "(bvmul accu_0_1 #x0001) "
                    "(ite exec_0_1_8 " // CMP
                      "(bvsub "
                        "accu_0_1 "
                        "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
                          "sb-val_0_1 "
                          "(select heap_0 #x0001))) "
                      "(ite exec_0_1_15 " // MEM
                        "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
                          "sb-val_0_1 "
                          "(select heap_0 #x0001)) "
                        "(ite exec_0_1_16 " // CAS
                          "(ite (= mem_0_1 (select heap_0 #x0001)) "
                            "#x0001 "
                            "#x0000) "
                          "accu_0_1))))))))))))\n"
    "(assert (= accu_1_2 "
      "(ite exec_0_2_0 " // LOAD
        "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
          "sb-val_0_2 "
          "(select heap_0 #x0001)) "
        "(ite exec_0_2_2 " // ADD
          "(bvadd "
            "accu_0_2 "
            "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
              "sb-val_0_2 "
              "(select heap_0 #x0001))) "
          "(ite exec_0_2_3 " // ADDI
            "(bvadd accu_0_2 #x0001) "
            "(ite exec_0_2_4 " // SUB
              "(bvsub "
                "accu_0_2 "
                "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
                  "sb-val_0_2 "
                  "(select heap_0 #x0001))) "
              "(ite exec_0_2_5 " // SUBI
                "(bvsub accu_0_2 #x0001) "
                "(ite exec_0_2_6 " // MUL
                  "(bvmul "
                    "accu_0_2 "
                    "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
                      "sb-val_0_2 "
                      "(select heap_0 #x0001))) "
                  "(ite exec_0_2_7 " // MULI
                    "(bvmul accu_0_2 #x0001) "
                    "(ite exec_0_2_8 " // CMP
                      "(bvsub "
                        "accu_0_2 "
                        "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
                          "sb-val_0_2 "
                          "(select heap_0 #x0001))) "
                      "(ite exec_0_2_15 " // MEM
                        "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
                          "sb-val_0_2 "
                          "(select heap_0 #x0001)) "
                        "(ite exec_0_2_16 " // CAS
                          "(ite (= mem_0_2 (select heap_0 #x0001)) "
                            "#x0001 "
                            "#x0000) "
                          "accu_0_2))))))))))))\n"
    "\n",
    encoder.str());

  // verbosity
  encoder = create<E>(dummy(1));

  verbose = false;
  encoder.define_accu();
  verbose = true;

  ASSERT_EQ(
    "(assert (= accu_1_0 (ite exec_0_0_0 (bvadd accu_0_0 #x0001) accu_0_0)))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::define_mem ==============================================

TEST(smtlib_Functional, define_mem)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  encoder.define_mem();

  ASSERT_EQ(
    "; mem variables - mem_<step>_<thread>\n"
    "(assert (= mem_1_0 "
      "(ite exec_0_0_15 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001)) "
        "mem_0_0)))\n"
    "(assert (= mem_1_1 "
      "(ite exec_0_1_15 "
        "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
          "sb-val_0_1 "
          "(select heap_0 #x0001)) "
        "mem_0_1)))\n"
    "(assert (= mem_1_2 "
      "(ite exec_0_2_15 "
        "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
          "sb-val_0_2 "
          "(select heap_0 #x0001)) "
        "mem_0_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_mem();
  verbose = true;

  ASSERT_EQ(
    "(assert (= mem_1_0 "
      "(ite exec_0_0_15 "
        "(ite (and sb-full_0_0 (= sb-adr_0_0 #x0001)) "
          "sb-val_0_0 "
          "(select heap_0 #x0001)) "
        "mem_0_0)))\n"
    "(assert (= mem_1_1 "
      "(ite exec_0_1_15 "
        "(ite (and sb-full_0_1 (= sb-adr_0_1 #x0001)) "
          "sb-val_0_1 "
          "(select heap_0 #x0001)) "
        "mem_0_1)))\n"
    "(assert (= mem_1_2 "
      "(ite exec_0_2_15 "
        "(ite (and sb-full_0_2 (= sb-adr_0_2 #x0001)) "
          "sb-val_0_2 "
          "(select heap_0 #x0001)) "
        "mem_0_2)))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::define_sb_adr ===========================================

TEST(smtlib_Functional, define_sb_adr)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  encoder.define_sb_adr();

  ASSERT_EQ(
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_1_0 (ite exec_0_0_1 #x0001 sb-adr_0_0)))\n"
    "(assert (= sb-adr_1_1 (ite exec_0_1_1 #x0001 sb-adr_0_1)))\n"
    "(assert (= sb-adr_1_2 (ite exec_0_2_1 #x0001 sb-adr_0_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_sb_adr();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-adr_1_0 (ite exec_0_0_1 #x0001 sb-adr_0_0)))\n"
    "(assert (= sb-adr_1_1 (ite exec_0_1_1 #x0001 sb-adr_0_1)))\n"
    "(assert (= sb-adr_1_2 (ite exec_0_2_1 #x0001 sb-adr_0_2)))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::define_sb_val ===========================================

TEST(smtlib_Functional, define_sb_val)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  encoder.define_sb_val();

  ASSERT_EQ(
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_1_0 (ite exec_0_0_1 accu_0_0 sb-val_0_0)))\n"
    "(assert (= sb-val_1_1 (ite exec_0_1_1 accu_0_1 sb-val_0_1)))\n"
    "(assert (= sb-val_1_2 (ite exec_0_2_1 accu_0_2 sb-val_0_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_sb_val();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-val_1_0 (ite exec_0_0_1 accu_0_0 sb-val_0_0)))\n"
    "(assert (= sb-val_1_1 (ite exec_0_1_1 accu_0_1 sb-val_0_1)))\n"
    "(assert (= sb-val_1_2 (ite exec_0_2_1 accu_0_2 sb-val_0_2)))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::define_sb_full ==========================================

TEST(smtlib_Functional, define_sb_full)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  encoder.define_sb_full();

  ASSERT_EQ(
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(assert (= sb-full_1_0 (ite flush_0_0 false (or exec_0_0_1 sb-full_0_0))))\n"
    "(assert (= sb-full_1_1 (ite flush_0_1 false (or exec_0_1_1 sb-full_0_1))))\n"
    "(assert (= sb-full_1_2 (ite flush_0_2 false (or exec_0_2_1 sb-full_0_2))))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_sb_full();
  verbose = true;

  ASSERT_EQ(
    "(assert (= sb-full_1_0 (ite flush_0_0 false (or exec_0_0_1 sb-full_0_0))))\n"
    "(assert (= sb-full_1_1 (ite flush_0_1 false (or exec_0_1_1 sb-full_0_1))))\n"
    "(assert (= sb-full_1_2 (ite flush_0_2 false (or exec_0_2_1 sb-full_0_2))))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_stmt)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "HALT\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(and stmt_0_0_1 (not exec_0_0_1)))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(and stmt_0_1_1 (not exec_0_1_1)))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(and stmt_0_2_1 (not exec_0_2_1)))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_stmt();
  verbose = true;

  ASSERT_EQ(
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(and stmt_0_0_1 (not exec_0_0_1)))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(and stmt_0_1_1 (not exec_0_1_1)))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(and stmt_0_2_1 (not exec_0_2_1)))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_stmt_jmp)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JMP 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(ite stmt_0_0_2 "
          "exec_0_0_2 "
          "(and stmt_0_0_1 (not exec_0_0_1))))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(ite stmt_0_1_2 "
          "exec_0_1_2 "
          "(and stmt_0_1_1 (not exec_0_1_1))))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(ite stmt_0_2_2 "
          "exec_0_2_2 "
          "(and stmt_0_2_1 (not exec_0_2_1))))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_stmt_jmp_conditional)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JNZ 1\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(ite stmt_0_0_2 "
          "(and exec_0_0_2 (not (= accu_0_0 #x0000))) "
          "(and stmt_0_0_1 (not exec_0_0_1))))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "(assert (= stmt_1_0_3 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (not (= accu_0_0 #x0000)))) "
        "(and stmt_0_0_3 (not exec_0_0_3)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(ite stmt_0_1_2 "
          "(and exec_0_1_2 (not (= accu_0_1 #x0000))) "
          "(and stmt_0_1_1 (not exec_0_1_1))))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "(assert (= stmt_1_1_3 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (not (= accu_0_1 #x0000)))) "
        "(and stmt_0_1_3 (not exec_0_1_3)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(ite stmt_0_2_2 "
          "(and exec_0_2_2 (not (= accu_0_2 #x0000))) "
          "(and stmt_0_2_1 (not exec_0_2_1))))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "(assert (= stmt_1_2_3 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (not (= accu_0_2 #x0000)))) "
        "(and stmt_0_2_3 (not exec_0_2_3)))))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_stmt_jmp_start)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JNZ 0\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (= accu_0_0 #x0000))) "
        "(and stmt_0_0_0 (not exec_0_0_0)))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(and stmt_0_0_1 (not exec_0_0_1)))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "(assert (= stmt_1_0_3 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (not (= accu_0_0 #x0000)))) "
        "(and stmt_0_0_3 (not exec_0_0_3)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (= accu_0_1 #x0000))) "
        "(and stmt_0_1_0 (not exec_0_1_0)))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(and stmt_0_1_1 (not exec_0_1_1)))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "(assert (= stmt_1_1_3 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (not (= accu_0_1 #x0000)))) "
        "(and stmt_0_1_3 (not exec_0_1_3)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (= accu_0_2 #x0000))) "
        "(and stmt_0_2_0 (not exec_0_2_0)))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(and stmt_0_2_1 (not exec_0_2_1)))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "(assert (= stmt_1_2_3 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (not (= accu_0_2 #x0000)))) "
        "(and stmt_0_2_3 (not exec_0_2_3)))))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_stmt_jmp_twice)
{
  const auto code =
    "ADDI 1\n"
    "STORE 1\n"
    "JZ 1\n"
    "JNZ 1\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_stmt();

  ASSERT_EQ(
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 "
      "(ite stmt_0_0_0 "
        "exec_0_0_0 "
        "(ite stmt_0_0_2 "
          "(and exec_0_0_2 (= accu_0_0 #x0000)) "
          "(ite stmt_0_0_3 "
            "(and exec_0_0_3 (not (= accu_0_0 #x0000))) "
            "(and stmt_0_0_1 (not exec_0_0_1)))))))\n"
    "(assert (= stmt_1_0_2 "
      "(ite stmt_0_0_1 "
        "exec_0_0_1 "
        "(and stmt_0_0_2 (not exec_0_0_2)))))\n"
    "(assert (= stmt_1_0_3 "
      "(ite stmt_0_0_2 "
        "(and exec_0_0_2 (not (= accu_0_0 #x0000))) "
        "(and stmt_0_0_3 (not exec_0_0_3)))))\n"
    "(assert (= stmt_1_0_4 "
      "(ite stmt_0_0_3 "
        "(and exec_0_0_3 (not (not (= accu_0_0 #x0000)))) "
        "(and stmt_0_0_4 (not exec_0_0_4)))))\n"
    "\n"
    "(assert (= stmt_1_1_0 (and stmt_0_1_0 (not exec_0_1_0))))\n"
    "(assert (= stmt_1_1_1 "
      "(ite stmt_0_1_0 "
        "exec_0_1_0 "
        "(ite stmt_0_1_2 "
          "(and exec_0_1_2 (= accu_0_1 #x0000)) "
          "(ite stmt_0_1_3 "
            "(and exec_0_1_3 (not (= accu_0_1 #x0000))) "
            "(and stmt_0_1_1 (not exec_0_1_1)))))))\n"
    "(assert (= stmt_1_1_2 "
      "(ite stmt_0_1_1 "
        "exec_0_1_1 "
        "(and stmt_0_1_2 (not exec_0_1_2)))))\n"
    "(assert (= stmt_1_1_3 "
      "(ite stmt_0_1_2 "
        "(and exec_0_1_2 (not (= accu_0_1 #x0000))) "
        "(and stmt_0_1_3 (not exec_0_1_3)))))\n"
    "(assert (= stmt_1_1_4 "
      "(ite stmt_0_1_3 "
        "(and exec_0_1_3 (not (not (= accu_0_1 #x0000)))) "
        "(and stmt_0_1_4 (not exec_0_1_4)))))\n"
    "\n"
    "(assert (= stmt_1_2_0 (and stmt_0_2_0 (not exec_0_2_0))))\n"
    "(assert (= stmt_1_2_1 "
      "(ite stmt_0_2_0 "
        "exec_0_2_0 "
        "(ite stmt_0_2_2 "
          "(and exec_0_2_2 (= accu_0_2 #x0000)) "
          "(ite stmt_0_2_3 "
            "(and exec_0_2_3 (not (= accu_0_2 #x0000))) "
            "(and stmt_0_2_1 (not exec_0_2_1)))))))\n"
    "(assert (= stmt_1_2_2 "
      "(ite stmt_0_2_1 "
        "exec_0_2_1 "
        "(and stmt_0_2_2 (not exec_0_2_2)))))\n"
    "(assert (= stmt_1_2_3 "
      "(ite stmt_0_2_2 "
        "(and exec_0_2_2 (not (= accu_0_2 #x0000))) "
        "(and stmt_0_2_3 (not exec_0_2_3)))))\n"
    "(assert (= stmt_1_2_4 "
      "(ite stmt_0_2_3 "
        "(and exec_0_2_3 (not (not (= accu_0_2 #x0000)))) "
        "(and stmt_0_2_4 (not exec_0_2_4)))))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::define_block ============================================

TEST(smtlib_Functional, define_block)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  encoder.define_block();

  ASSERT_EQ(
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(assert (= block_1_1_0 (ite check_0_1 false (or exec_0_0_17 block_0_1_0))))\n"
    "(assert (= block_1_1_1 (ite check_0_1 false (or exec_0_1_17 block_0_1_1))))\n"
    "(assert (= block_1_1_2 (ite check_0_1 false (or exec_0_2_17 block_0_1_2))))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_block();
  verbose = true;

  ASSERT_EQ(
    "(assert (= block_1_1_0 (ite check_0_1 false (or exec_0_0_17 block_0_1_0))))\n"
    "(assert (= block_1_1_1 (ite check_0_1 false (or exec_0_1_17 block_0_1_1))))\n"
    "(assert (= block_1_1_2 (ite check_0_1 false (or exec_0_2_17 block_0_1_2))))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_block_empty)
{
  auto encoder = create<E>();

  encoder.define_block();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Functional::define_halt =============================================

TEST(smtlib_Functional, define_halt)
{
  const auto code =
    "ADDI 1\n"
    "JNZ 3\n"
    "HALT\n"
    "SUBI 1\n"
    "HALT\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_halt();

  ASSERT_EQ(
    "; halt variables - halt_<step>_<thread>\n"
    "(assert (= halt_1_0 (or exec_0_0_2 exec_0_0_4 halt_0_0)))\n"
    "(assert (= halt_1_1 (or exec_0_1_2 exec_0_1_4 halt_0_1)))\n"
    "(assert (= halt_1_2 (or exec_0_2_2 exec_0_2_4 halt_0_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_halt();
  verbose = true;

  ASSERT_EQ(
    "(assert (= halt_1_0 (or exec_0_0_2 exec_0_0_4 halt_0_0)))\n"
    "(assert (= halt_1_1 (or exec_0_1_2 exec_0_1_4 halt_0_1)))\n"
    "(assert (= halt_1_2 (or exec_0_2_2 exec_0_2_4 halt_0_2)))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_halt_empty)
{
  auto encoder = create<E>();

  encoder.define_halt();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Functional::define_heap =============================================

TEST(smtlib_Functional, define_heap)
{
  auto encoder = create<E>(dup(prog(instruction_set), 3));

  encoder.define_heap();

  ASSERT_EQ(
    "; heap variable - heap_<step>\n"
    "(assert (= heap_1 "
      "(ite flush_0_0 " // FLUSH
        "(store heap_0 sb-adr_0_0 sb-val_0_0) "
        "(ite exec_0_0_16 " // CAS
          "(ite (= mem_0_0 (select heap_0 #x0001)) "
            "(store heap_0 #x0001 accu_0_0) "
            "heap_0) "
          "(ite flush_0_1 " // FLUSH
            "(store heap_0 sb-adr_0_1 sb-val_0_1) "
            "(ite exec_0_1_16 " // CAS
              "(ite (= mem_0_1 (select heap_0 #x0001)) "
                "(store heap_0 #x0001 accu_0_1) "
                "heap_0) "
              "(ite flush_0_2 " // FLUSH
                "(store heap_0 sb-adr_0_2 sb-val_0_2) "
                "(ite exec_0_2_16 " // CAS
                  "(ite (= mem_0_2 (select heap_0 #x0001)) "
                    "(store heap_0 #x0001 accu_0_2) "
                    "heap_0) "
                  "heap_0))))))))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_heap();
  verbose = true;

  ASSERT_EQ(
    "(assert (= heap_1 "
      "(ite flush_0_0 " // FLUSH
        "(store heap_0 sb-adr_0_0 sb-val_0_0) "
        "(ite exec_0_0_16 " // CAS
          "(ite (= mem_0_0 (select heap_0 #x0001)) "
            "(store heap_0 #x0001 accu_0_0) "
            "heap_0) "
          "(ite flush_0_1 " // FLUSH
            "(store heap_0 sb-adr_0_1 sb-val_0_1) "
            "(ite exec_0_1_16 " // CAS
              "(ite (= mem_0_1 (select heap_0 #x0001)) "
                "(store heap_0 #x0001 accu_0_1) "
                "heap_0) "
              "(ite flush_0_2 " // FLUSH
                "(store heap_0 sb-adr_0_2 sb-val_0_2) "
                "(ite exec_0_2_16 " // CAS
                  "(ite (= mem_0_2 (select heap_0 #x0001)) "
                    "(store heap_0 #x0001 accu_0_2) "
                    "heap_0) "
                  "heap_0))))))))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::define_exit_flag ========================================

TEST(smtlib_Functional, define_exit_flag)
{
  const auto code =
    "JNZ 2\n"
    "HALT\n"
    "EXIT 1\n";

  auto encoder = create<E>(dup(prog(code), 3));

  encoder.define_exit_flag();

  ASSERT_EQ(
    "; exit flag variable - exit_<step>\n"
    "(assert (= exit_1 (or "
      "exit_0 "
      "(and halt_1_0 halt_1_1 halt_1_2) "
      "exec_0_0_2 exec_0_1_2 exec_0_2_2)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_exit_flag();
  verbose = true;

  ASSERT_EQ(
    "(assert (= exit_1 (or "
      "exit_0 "
      "(and halt_1_0 halt_1_1 halt_1_2) "
      "exec_0_0_2 exec_0_1_2 exec_0_2_2)))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_exit_flag_empty)
{
  auto encoder = create<E>();

  encoder.define_exit_flag();

  ASSERT_EQ("", encoder.formula.str());
}

// smtlib::Functional::define_exit_code ========================================

TEST(smtlib_Functional, define_exit_code)
{
  auto encoder = create<E>(lst(prog("EXIT 0"), prog("EXIT 1"), prog("EXIT 2")));

  encoder.define_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (= exit-code "
      "(ite exec_1_0_0 "
        "#x0000 "
        "(ite exec_1_1_0 "
          "#x0001 "
          "(ite exec_1_2_0 "
            "#x0002 "
            "#x0000)))))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_exit_code();
  verbose = true;

  ASSERT_EQ(
    "(assert (= exit-code "
      "(ite exec_1_0_0 "
        "#x0000 "
        "(ite exec_1_1_0 "
          "#x0001 "
          "(ite exec_1_2_0 "
            "#x0002 "
            "#x0000)))))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_exit_code_empty)
{
  auto encoder = create<E>();

  encoder.define_exit_code();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; exit code\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "(assert (= exit-code #x0000))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::define_states ===========================================

TEST(smtlib_Functional, define_states)
{
  auto encoder = create<E>(lst(prog("JMP 0")));

  encoder.define_states();

  ASSERT_EQ(
    "; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu variables - accu_<step>_<thread>\n"
    "(assert (= accu_1_0 accu_0_0))\n"
    "\n"
    "; mem variables - mem_<step>_<thread>\n"
    "(assert (= mem_1_0 mem_0_0))\n"
    "\n"
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_1_0 sb-adr_0_0))\n"
    "\n"
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_1_0 sb-val_0_0))\n"
    "\n"
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(assert (= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)))\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (ite stmt_0_0_0 exec_0_0_0 (and stmt_0_0_0 (not exec_0_0_0)))))\n"
    "\n"
    "; heap variable - heap_<step>\n"
    "(assert (= heap_1 (ite flush_0_0 (store heap_0 sb-adr_0_0 sb-val_0_0) heap_0)))\n"
    "\n",
    encoder.str());

  // verbosity
  reset(encoder);

  verbose = false;
  encoder.define_states();
  verbose = true;

  ASSERT_EQ(
    "(assert (= accu_1_0 accu_0_0))\n"
    "\n"
    "(assert (= mem_1_0 mem_0_0))\n"
    "\n"
    "(assert (= sb-adr_1_0 sb-adr_0_0))\n"
    "\n"
    "(assert (= sb-val_1_0 sb-val_0_0))\n"
    "\n"
    "(assert (= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)))\n"
    "\n"
    "(assert (= stmt_1_0_0 (ite stmt_0_0_0 exec_0_0_0 (and stmt_0_0_0 (not exec_0_0_0)))))\n"
    "\n"
    "(assert (= heap_1 (ite flush_0_0 (store heap_0 sb-adr_0_0 sb-val_0_0) heap_0)))\n"
    "\n",
    encoder.str());
}

TEST(smtlib_Functional, define_states_check_exit)
{
  const auto code =
    "CHECK 0\n"
    "EXIT 1\n";

  auto encoder = create<E>(lst(prog(code)));

  encoder.define_states();

  ASSERT_EQ(
    "; state variable definitions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; accu variables - accu_<step>_<thread>\n"
    "(assert (= accu_1_0 accu_0_0))\n"
    "\n"
    "; mem variables - mem_<step>_<thread>\n"
    "(assert (= mem_1_0 mem_0_0))\n"
    "\n"
    "; store buffer address variables - sb-adr_<step>_<thread>\n"
    "(assert (= sb-adr_1_0 sb-adr_0_0))\n"
    "\n"
    "; store buffer value variables - sb-val_<step>_<thread>\n"
    "(assert (= sb-val_1_0 sb-val_0_0))\n"
    "\n"
    "; store buffer full variables - sb-full_<step>_<thread>\n"
    "(assert (= sb-full_1_0 (ite flush_0_0 false sb-full_0_0)))\n"
    "\n"
    "; statement activation variables - stmt_<step>_<thread>_<pc>\n"
    "(assert (= stmt_1_0_0 (and stmt_0_0_0 (not exec_0_0_0))))\n"
    "(assert (= stmt_1_0_1 (ite stmt_0_0_0 exec_0_0_0 (and stmt_0_0_1 (not exec_0_0_1)))))\n"
    "\n"
    "; blocking variables - block_<step>_<id>_<thread>\n"
    "(assert (= block_1_0_0 (ite check_0_0 false (or exec_0_0_0 block_0_0_0))))\n"
    "\n"
    "; heap variable - heap_<step>\n"
    "(assert (= heap_1 (ite flush_0_0 (store heap_0 sb-adr_0_0 sb-val_0_0) heap_0)))\n"
    "\n"
    "; exit flag variable - exit_<step>\n"
    "(assert (= exit_1 (or exit_0 exec_0_0_1)))\n"
    "\n",
    encoder.str());
}

// smtlib::Functional::encode ==================================================

TEST(smtlib_Functional, encode_check)
{
  encode_check<E>("increment.check.functional.t2.k16.smt2");
}

TEST(smtlib_Functional, encode_cas)
{
  encode_cas<E>("increment.cas.functional.t2.k16.smt2");
}

TEST(smtlib_Functional, encode_halt)
{
  encode_halt<E>("halt.functional.t2.k10.smt2");
}

const std::string formula = "formula.functional.smt2";

TEST(smtlib_Functional, litmus_intel_1) { litmus_intel_1<E>(formula); }
TEST(smtlib_Functional, litmus_intel_2) { litmus_intel_2<E>(formula); }
TEST(smtlib_Functional, litmus_intel_3) { litmus_intel_3<E>(formula); }
TEST(smtlib_Functional, litmus_intel_4) { litmus_intel_4<E>(formula); }
TEST(smtlib_Functional, litmus_intel_5) { litmus_intel_5<E>(formula); }
TEST(smtlib_Functional, litmus_intel_6) { litmus_intel_6<E>(formula); }
TEST(smtlib_Functional, litmus_intel_7) { litmus_intel_7<E>(formula); }

} // namespace ConcuBinE::test
