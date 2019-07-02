#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "streamredirecter.hh"

#include "publicate.hh"
#include "cvc4.hh"

namespace test {

//==============================================================================
// CVC4 tests
//==============================================================================

struct CVC4 : public ::testing::Test
{
  ::CVC4 cvc4;
};

TEST_F(CVC4, sat)
{
  std::string formula = "(set-logic QF_AUFBV)(assert true)(check-sat)";

  std::ostringstream ss;
  StreamRedirecter redirecter(std::cout, ss);

  redirecter.start();

  ASSERT_TRUE(cvc4.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", cvc4.std_out.str());
}

TEST_F(CVC4, unsat)
{
  std::string formula = "(set-logic QF_AUFBV)(assert false)(check-sat)";

  std::ostringstream ss;
  StreamRedirecter redirecter(std::cout, ss);

  redirecter.start();

  ASSERT_FALSE(cvc4.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", cvc4.std_out.str());
}

// TODO: remove
TEST_F(CVC4, print_model)
{
  // concurrent increment using CHECK
  std::string constraints;
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  Program::List::ptr programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  Encoder::ptr encoder = std::make_unique<smtlib::Functional>(programs, 12);

  std::string formula = cvc4.build_formula(*encoder, constraints);

  bool sat = cvc4.sat(formula);

  std::cout << cvc4.std_out.str();

  ASSERT_TRUE(sat);
}

} // namespace test
