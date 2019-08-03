#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "simulator.hh"

#include "publicate.hh"
#include "cvc4.hh"

namespace ConcuBinE::test {

//==============================================================================
// CVC4 tests
//==============================================================================

struct CVC4 : public ::testing::Test
{
  ConcuBinE::CVC4 cvc4;
  Encoder::ptr encoder;
  Program::List::ptr programs = std::make_shared<Program::List>();
  Trace::ptr trace;
};

TEST_F(CVC4, sat)
{
  ASSERT_TRUE(cvc4.sat("(set-logic QF_AUFBV)(assert true)(check-sat)"));
  ASSERT_EQ("sat\n", cvc4.std_out.str());
}

TEST_F(CVC4, unsat)
{
  ASSERT_FALSE(cvc4.sat("(set-logic QF_AUFBV)(assert false)(check-sat)"));
  ASSERT_EQ("unsat\n", cvc4.std_out.str());
}

TEST_F(CVC4, solve_check)
{
  // concurrent increment using CHECK
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = cvc4.solve(*encoder);

  std::cout << "time to solve = " << cvc4.time << " ms" << eol;

  // std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(CVC4, solve_cas)
{
  // concurrent increment using CAS
  std::string increment = "data/increment.cas.asm";

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = cvc4.solve(*encoder);

  std::cout << "time to solve = " << cvc4.time << " ms" << eol;

  // std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(CVC4, DISABLED_solve_multiple_addresses)
{
  std::istringstream p0 (
    "STORE 0\n"
    "ADDI 1\n"
    "STORE 0\n"
    "HALT\n");
  std::istringstream p1 (
    "STORE 1\n"
    "ADDI 1\n"
    "STORE 1\n"
    "HALT\n");

  programs->push_back(Program(p0, "load.store.0.asm"));
  programs->push_back(Program(p1, "load.store.1.asm"));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = cvc4.solve(*encoder);

  std::cout << "time to solve = " << cvc4.time << " ms" << eol;

  std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(CVC4, solve_indirect_uninitialized)
{
  std::istringstream p0 (
    "LOAD [0]\n"
    "ADDI 1\n"
    "STORE [0]\n"
    "HALT\n");
  std::istringstream p1 (
    "LOAD [1]\n"
    "ADDI 1\n"
    "STORE [1]\n"
    "HALT\n");

  programs->push_back(Program(p0, "load.store.0.asm"));
  programs->push_back(Program(p1, "load.store.1.asm"));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = cvc4.solve(*encoder);

  std::cout << "time to solve = " << cvc4.time << " ms" << eol;

  std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

// TODO: remove
TEST_F(CVC4, print_model_check)
{
  // concurrent increment using CHECK
  std::string constraints;
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  bool sat = cvc4.sat(cvc4.build_formula(*encoder, constraints));

  std::ofstream outfile("/tmp/cvc4.check.out");
  outfile << cvc4.std_out.str();

  ASSERT_TRUE(sat);
}

TEST_F(CVC4, print_model_cas)
{
  // concurrent increment using CAS
  std::string constraints;
  std::string increment_cas = "data/increment.cas.asm";

  programs->push_back(create_from_file<Program>(increment_cas));
  programs->push_back(create_from_file<Program>(increment_cas));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  bool sat = cvc4.sat(cvc4.build_formula(*encoder, constraints));

  std::ofstream outfile("/tmp/cvc4.cas.out");
  outfile << cvc4.std_out.str();

  ASSERT_TRUE(sat);
}

TEST_F(CVC4, DISABLED_print_multiple_addresses)
{
  std::istringstream p0 (
    "STORE 0\n"
    "ADDI 1\n"
    "STORE 0\n"
    "HALT\n");
  std::istringstream p1 (
    "STORE 1\n"
    "ADDI 1\n"
    "STORE 1\n"
    "HALT\n");

  programs->push_back(Program(p0, "dummy.asm"));
  programs->push_back(Program(p1, "dummy.asm"));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  bool sat = cvc4.sat(cvc4.build_formula(*encoder, ""));

  std::ofstream outfile("/tmp/cvc4.multiple-addresses.out");
  outfile << cvc4.std_out.str();

  ASSERT_TRUE(sat);
}

TEST_F(CVC4, DISABLED_print_indirect_uninitialized)
{
  std::istringstream p0 (
    "LOAD [0]\n"
    "ADDI 1\n"
    "STORE [0]\n"
    "HALT\n");
  std::istringstream p1 (
    "LOAD [1]\n"
    "ADDI 1\n"
    "STORE [1]\n"
    "HALT\n");

  programs->push_back(Program(p0, "dummy.asm"));
  programs->push_back(Program(p1, "dummy.asm"));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  std::string formula = cvc4.build_formula(*encoder, "");

  std::ofstream f("/tmp/cvc4.indirect.uninitialized.smt2");
  f << formula;

  bool sat = cvc4.sat(formula);

  std::ofstream outfile("/tmp/cvc4.indirect.uninitialized.out");
  outfile << cvc4.std_out.str();

  ASSERT_TRUE(sat);
}

} // namespace ConcuBinE::test
