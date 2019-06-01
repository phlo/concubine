#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "streamredirecter.hh"

#include "publicate.hh"
#include "cvc4.hh"

using namespace std;

struct CVC4Test : public ::testing::Test
{
  CVC4 cvc4;
};

TEST_F(CVC4Test, sat)
{
  string formula = "(set-logic QF_AUFBV)(assert true)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(cvc4.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", cvc4.std_out.str());
}

TEST_F(CVC4Test, unsat)
{
  string formula = "(set-logic QF_AUFBV)(assert false)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(cvc4.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", cvc4.std_out.str());
}

// TODO: remove
TEST_F(CVC4Test, print_model)
{
  /* concurrent increment using CHECK */
  string constraints;
  string increment_0 = "data/increment.check.thread.0.asm";
  string increment_n = "data/increment.check.thread.n.asm";

  Program_list_ptr programs = make_shared<Program_list>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  Encoder_ptr encoder = make_shared<SMTLibEncoderFunctional>(programs, 12);

  string formula = cvc4.build_formula(*encoder, constraints);

  bool sat = cvc4.sat(formula);

  cout << cvc4.std_out.str();

  ASSERT_TRUE(sat);
}
