#include <gtest/gtest.h>

#include "btormc.hh"
#include "encoder.hh"
#include "parser.hh"
#include "simulator.hh"

namespace ConcuBinE::test {

//==============================================================================
// BtorMC tests
//==============================================================================

struct BtorMC : public ::testing::Test
{
  ConcuBinE::BtorMC btormc = ConcuBinE::BtorMC(16);
  Encoder::ptr encoder;
  Program::List::ptr programs = std::make_shared<Program::List>();
  Trace::ptr trace;
};

TEST_F(BtorMC, sat)
{
  std::string formula =
    "1 sort bitvec 1\n"
    "2 state 1 x\n"
    "3 bad 2\n";

  ASSERT_TRUE(btormc.sat(formula));
  ASSERT_EQ(
    "sat\n"
    "b0 \n"
    "#0\n"
    "0 1 x#0\n"
    "@0\n"
    ".\n",
    btormc.std_out.str());
}

TEST_F(BtorMC, unsat)
{
  std::string formula =
    "1 sort bitvec 1\n"
    "2 state 1 x\n";

  ASSERT_FALSE(btormc.sat(formula));
  ASSERT_EQ("", btormc.std_out.str());
}

TEST_F(BtorMC, solve_check)
{
  // concurrent increment using CHECK
  std::string constraints;
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<btor2::Encoder>(programs, 16);

  trace = btormc.solve(*encoder, constraints);

  // std::cout << trace->print();

  Simulator simulator {programs};

  Trace::ptr replay {simulator.replay(*trace)};

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

TEST_F(BtorMC, solve_cas)
{
  // concurrent increment using CAS
  std::string constraints;
  std::string increment = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = std::make_unique<btor2::Encoder>(programs, 16);

  trace = btormc.solve(*encoder, constraints);

  // std::cout << trace->print();

  Simulator simulator {programs};

  Trace::ptr replay {simulator.replay(*trace)};

  // std::cout << replay->print();

  ASSERT_EQ(*replay, *trace);
}

// TODO: remove
TEST_F(BtorMC, print_model_check)
{
  // concurrent increment using CHECK
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<btor2::Encoder>(programs, 16);

  std::string formula = btormc.build_formula(*encoder, "");

  bool sat = btormc.sat(formula);

  std::ofstream trace_file("/tmp/btormc.check.out");
  trace_file << btormc.std_out.str();

  ASSERT_TRUE(sat);
}

TEST_F(BtorMC, print_model_cas)
{
  // concurrent increment using CAS
  std::string increment_cas = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_cas));
  programs->push_back(create_from_file<Program>(increment_cas));

  encoder = std::make_unique<btor2::Encoder>(programs, 16);

  std::string formula = btormc.build_formula(*encoder, "");

  bool sat = btormc.sat(formula);

  std::ofstream trace_file("/tmp/btormc.cas.out");
  trace_file << btormc.std_out.str();

  ASSERT_TRUE(sat);
}

} // namespace ConcuBinE::test
