#include "test_solver.hh"

#include "z3.hh"

namespace ConcuBinE::test {

//==============================================================================
// Z3 tests
//==============================================================================

using Z3 = Solver<Z3>;

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

using F = smtlib::Functional;
using R = smtlib::Relational;

// simulation tests
//
TEST_F(Z3, solve_check_functional) { solve_check<F>(); }
TEST_F(Z3, solve_check_relational) { solve_check<R>(); }

TEST_F(Z3, solve_cas_functional) { solve_cas<F>(); }
TEST_F(Z3, solve_cas_relational) { solve_cas<R>(); }

TEST_F(Z3, solve_indirect_functional) { solve_indirect<F>(); }
TEST_F(Z3, solve_indirect_relational) { solve_indirect<R>(); }

TEST_F(Z3, solve_halt_functional) { solve_halt<F>(); }
TEST_F(Z3, solve_halt_relational) { solve_halt<R>(); }

// litmus tests
//
TEST_F(Z3, litmus_intel_1_functional) { litmus_intel_1<F>(); }
TEST_F(Z3, litmus_intel_1_relational) { litmus_intel_1<R>(); }

TEST_F(Z3, litmus_intel_2_functional) { litmus_intel_2<F>(); }
TEST_F(Z3, litmus_intel_2_relational) { litmus_intel_2<R>(); }

TEST_F(Z3, litmus_intel_3_functional) { litmus_intel_3<F>(); }
TEST_F(Z3, litmus_intel_3_relational) { litmus_intel_3<R>(); }

TEST_F(Z3, litmus_intel_4_functional) { litmus_intel_4<F>(); }
TEST_F(Z3, litmus_intel_4_relational) { litmus_intel_4<R>(); }

TEST_F(Z3, litmus_intel_5_functional) { litmus_intel_5<F>(); }
TEST_F(Z3, litmus_intel_5_relational) { litmus_intel_5<R>(); }

TEST_F(Z3, litmus_intel_6_functional) { litmus_intel_6<F>(); }
TEST_F(Z3, litmus_intel_6_relational) { litmus_intel_6<R>(); }

TEST_F(Z3, litmus_intel_7_functional) { litmus_intel_7<F>(); }
TEST_F(Z3, litmus_intel_7_relational) { litmus_intel_7<R>(); }

} // namespace ConcuBinE::test
