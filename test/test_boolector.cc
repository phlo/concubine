#include <gtest/gtest.h>

#include "boolector.hh"
#include "encoder.hh"
#include "parser.hh"
#include "simulator.hh"

namespace ConcuBinE::test {

//==============================================================================
// Boolector tests
//==============================================================================

struct Boolector : public ::testing::Test
{
  ConcuBinE::Boolector boolector;
  Encoder::ptr encoder;
  Program::List::ptr programs = std::make_shared<Program::List>();
  Trace::ptr trace;
};

TEST_F(Boolector, sat)
{
  ASSERT_TRUE(boolector.sat("(assert true)(check-sat)"));
  ASSERT_EQ("sat\n", boolector.std_out.str());
}

TEST_F(Boolector, unsat)
{
  ASSERT_FALSE(boolector.sat("(assert false)(check-sat)"));
  ASSERT_EQ("unsat\n", boolector.std_out.str());
}

TEST_F(Boolector, solve_check)
{
  // concurrent increment using CHECK
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<smtlib::Functional>(programs, nullptr, 16);

  trace = boolector.solve(*encoder);

  // std::cout << "time to solve = " << boolector.time << " ms" << eol;

  // std::cout << trace->print();

  Trace::ptr replay = Simulator().replay(*trace);

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(Boolector, solve_cas)
{
  // concurrent increment using CAS
  std::string increment = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = std::make_unique<smtlib::Functional>(programs, nullptr, 16);

  trace = boolector.solve(*encoder);

  // std::cout << "time to solve = " << boolector.time << " ms" << eol;

  // std::cout << trace->print();

  Trace::ptr replay = Simulator().replay(*trace);

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(Boolector, solve_indirect_uninitialized)
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

  encoder = std::make_unique<smtlib::Functional>(programs, nullptr, 16);

  trace = boolector.solve(*encoder);

  // std::cout << "time to solve = " << boolector.time << " ms" << eol;

  // std::cout << trace->print();

  Trace::ptr replay = Simulator().replay(*trace);

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

// TODO: remove
TEST_F(Boolector, print_model_check)
{
  // concurrent increment using CHECK
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<smtlib::Functional>(programs, nullptr, 16);

  std::string formula = boolector.formula(*encoder, "");

  bool sat = boolector.sat(formula);

  std::ofstream outfile("/tmp/boolector.check.out");
  outfile << boolector.std_out.str();

  ASSERT_TRUE(sat);
}

TEST_F(Boolector, print_model_cas)
{
  // concurrent increment using CAS
  std::string increment_cas = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_cas));
  programs->push_back(create_from_file<Program>(increment_cas));

  encoder = std::make_unique<smtlib::Functional>(programs, nullptr, 16);

  std::string formula = boolector.formula(*encoder, "");

  bool sat = boolector.sat(formula);

  std::ofstream out("/tmp/boolector.cas.out");
  out << boolector.std_out.str();

  ASSERT_TRUE(sat);
}

} // namespace ConcuBinE::test
