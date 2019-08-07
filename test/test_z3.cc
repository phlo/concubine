#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "simulator.hh"
#include "z3.hh"

namespace ConcuBinE::test {

//==============================================================================
// Z3 tests
//==============================================================================

struct Z3 : public ::testing::Test
{
  ConcuBinE::Z3 z3;
  Encoder::ptr encoder;
  Program::List::ptr programs = std::make_shared<Program::List>();
  Trace::ptr trace;
};

TEST_F(Z3, sat)
{
  ASSERT_TRUE(z3.sat("(assert true)(check-sat)"));
}

TEST_F(Z3, unsat)
{
  ASSERT_FALSE(z3.sat("(assert false)(check-sat)"));
}

TEST_F(Z3, solve_check)
{
  // concurrent increment using CHECK
  std::string constraints;
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = z3.solve(*encoder, constraints);

  // std::cout << "time to solve = " << z3.time << " ms" << eol;

  // std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(Z3, solve_cas)
{
  // concurrent increment using CAS
  std::string constraints;
  std::string increment = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = z3.solve(*encoder, constraints);

  // std::cout << "time to solve = " << z3.time << " ms" << eol;

  // std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(Z3, solve_indirect_uninitialized)
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

  trace = z3.solve(*encoder);

  // std::cout << "time to solve = " << z3.time << " ms" << eol;

  // std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

} // namespace ConcuBinE::test
