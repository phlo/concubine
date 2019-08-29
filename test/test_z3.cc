#include "test_solver.hh"

#include "z3.hh"

namespace ConcuBinE::test {

//==============================================================================
// Z3 tests
//==============================================================================

using Z3 = Solver<Z3, smtlib::Functional>;

// Z3::sat =====================================================================

TEST_F(Z3, sat)
{
  ASSERT_TRUE(solver.sat("(assert true)(check-sat)"));
}

TEST_F(Z3, unsat)
{
  ASSERT_FALSE(solver.sat("(assert false)(check-sat)"));
}

// Z3::solve ===================================================================

TEST_F(Z3, solve_check) { solve_check(); }
TEST_F(Z3, solve_cas) { solve_cas(); }
TEST_F(Z3, solve_indirect) { solve_indirect(); }

TEST_F(Z3, litmus_intel_1) { litmus_intel_1(); }
TEST_F(Z3, litmus_intel_2) { litmus_intel_2(); }
TEST_F(Z3, litmus_intel_3) { litmus_intel_3(); }
TEST_F(Z3, litmus_intel_4) { litmus_intel_4(); }
TEST_F(Z3, litmus_intel_5) { litmus_intel_5(); }
TEST_F(Z3, litmus_intel_6) { litmus_intel_6(); }

} // namespace ConcuBinE::test
