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
  std::string constraints;
  ConcuBinE::Boolector boolector;
  Encoder::ptr encoder;
  Program::List::ptr programs = std::make_shared<Program::List>();
  Trace::ptr trace;
};

TEST_F(Boolector, sat)
{
  std::string formula = "(assert true)(check-sat)";

  ASSERT_TRUE(boolector.sat(formula));

  ASSERT_EQ("sat\n", boolector.std_out.str());
}

TEST_F(Boolector, unsat)
{
  std::string formula = "(assert false)(check-sat)";

  ASSERT_FALSE(boolector.sat(formula));

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

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = boolector.solve(*encoder, constraints);

  // std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

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

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  trace = boolector.solve(*encoder, constraints);

  // std::cout << trace->print();

  Simulator simulator (programs);

  Trace::ptr replay (simulator.replay(*trace));

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(Boolector, DISABLED_encode_deadlock)
{
  // deadlock after 3 steps -> unsat
  programs->push_back(create_from_file<Program>("data/deadlock.thread.0.asm"));
  programs->push_back(create_from_file<Program>("data/deadlock.thread.1.asm"));

  encoder = std::make_unique<smtlib::Functional>(programs, 3);

  std::string formula = encoder->str();

  ASSERT_FALSE(boolector.sat(formula));
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

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  std::string formula = boolector.build_formula(*encoder, constraints);

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

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  std::string formula = boolector.build_formula(*encoder, constraints);

  bool sat = boolector.sat(formula);

  std::ofstream outfile("/tmp/boolector.cas.out");
  outfile << boolector.std_out.str();

  ASSERT_TRUE(sat);
}

} // namespace ConcuBinE::test
