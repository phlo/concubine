#include "test_solver.hh"

#include "boolector.hh"

namespace ConcuBinE::test {

//==============================================================================
// Boolector tests
//==============================================================================

using Boolector = Solver<Boolector, smtlib::Functional>;

// Boolector::sat ==============================================================

TEST_F(Boolector, sat)
{
  ASSERT_TRUE(solver.sat("(assert true)(check-sat)"));
  ASSERT_EQ("sat\n", solver.std_out.str());
}

TEST_F(Boolector, unsat)
{
  ASSERT_FALSE(solver.sat("(assert false)(check-sat)"));
  ASSERT_EQ("unsat\n", solver.std_out.str());
}

// Boolector::solve ============================================================

TEST_F(Boolector, solve_check) { solve_check(); }
TEST_F(Boolector, solve_cas) { solve_cas(); }
TEST_F(Boolector, solve_indirect) { solve_indirect(); }

TEST_F(Boolector, litmus_intel_1) { litmus_intel_1(); }
TEST_F(Boolector, litmus_intel_2) { litmus_intel_2(); }
TEST_F(Boolector, litmus_intel_3) { litmus_intel_3(); }

} // namespace ConcuBinE::test
