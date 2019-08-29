#include "test_solver.hh"

#include "cvc4.hh"

namespace ConcuBinE::test {

//==============================================================================
// CVC4 tests
//==============================================================================

using CVC4 = Solver<CVC4, smtlib::Functional>;

// CVC4::sat ===================================================================

TEST_F(CVC4, sat)
{
  ASSERT_TRUE(solver.sat("(set-logic QF_AUFBV)(assert true)(check-sat)"));
  ASSERT_EQ("sat\n", solver.std_out.str());
}

TEST_F(CVC4, unsat)
{
  ASSERT_FALSE(solver.sat("(set-logic QF_AUFBV)(assert false)(check-sat)"));
  ASSERT_EQ("unsat\n", solver.std_out.str());
}

// CVC4::solve =================================================================

TEST_F(CVC4, solve_check) { solve_check(); }
TEST_F(CVC4, solve_cas) { solve_cas(); }
TEST_F(CVC4, solve_indirect) { solve_indirect(); }

TEST_F(CVC4, litmus_intel_1) { litmus_intel_1(); }
TEST_F(CVC4, litmus_intel_2) { litmus_intel_2(); }
TEST_F(CVC4, litmus_intel_3) { litmus_intel_3(); }
TEST_F(CVC4, litmus_intel_4) { litmus_intel_4(); }
TEST_F(CVC4, litmus_intel_5) { litmus_intel_5(); }

} // namespace ConcuBinE::test
