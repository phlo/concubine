#include "test_solver.hh"

#include "cvc4.hh"

namespace ConcuBinE::test {

//==============================================================================
// CVC4 tests
//==============================================================================

using CVC4 = Solver<CVC4>;

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

using F = smtlib::Functional;
using R = smtlib::Relational;

// simulation tests
//
TEST_F(CVC4, solve_check_functional) { solve_check<F>(); }
TEST_F(CVC4, solve_check_relational) { solve_check<R>(); }

TEST_F(CVC4, solve_cas_functional) { solve_cas<F>(); }
TEST_F(CVC4, solve_cas_relational) { solve_cas<R>(); }

TEST_F(CVC4, solve_indirect_functional) { solve_indirect<F>(); }
TEST_F(CVC4, solve_indirect_relational) { solve_indirect<R>(); }

TEST_F(CVC4, solve_halt_functional) { solve_halt<F>(); }
TEST_F(CVC4, solve_halt_relational) { solve_halt<R>(); }

// litmus tests
//
TEST_F(CVC4, litmus_intel_1_functional) { litmus_intel_1<F>(); }
TEST_F(CVC4, litmus_intel_1_relational) { litmus_intel_1<R>(); }

TEST_F(CVC4, litmus_intel_2_functional) { litmus_intel_2<F>(); }
TEST_F(CVC4, litmus_intel_2_relational) { litmus_intel_2<R>(); }

TEST_F(CVC4, litmus_intel_3_functional) { litmus_intel_3<F>(); }
TEST_F(CVC4, litmus_intel_3_relational) { litmus_intel_3<R>(); }

TEST_F(CVC4, litmus_intel_4_functional) { litmus_intel_4<F>(); }
TEST_F(CVC4, litmus_intel_4_relational) { litmus_intel_4<R>(); }

TEST_F(CVC4, DISABLED_litmus_intel_5_functional) { litmus_intel_5<F>(); } // ~30s
TEST_F(CVC4, litmus_intel_5_relational) { litmus_intel_5<R>(); }

TEST_F(CVC4, litmus_intel_6_functional) { litmus_intel_6<F>(); }
TEST_F(CVC4, litmus_intel_6_relational) { litmus_intel_6<R>(); }

TEST_F(CVC4, DISABLED_litmus_intel_7_functional) { litmus_intel_7<F>(); } // ~1h 23m !!
TEST_F(CVC4, DISABLED_litmus_intel_7_relational) { litmus_intel_7<R>(); } // ??

TEST_F(CVC4, DISABLED_litmus_intel_8_functional) { litmus_intel_8<F>(); } // ??
TEST_F(CVC4, DISABLED_litmus_intel_8_relational) { litmus_intel_8<R>(); } // ??

TEST_F(CVC4, litmus_intel_9_functional) { litmus_intel_9<F>(); }
TEST_F(CVC4, litmus_intel_9_relational) { litmus_intel_9<R>(); }

TEST_F(CVC4, litmus_intel_10_functional) { litmus_intel_10<F>(); }
TEST_F(CVC4, litmus_intel_10_relational) { litmus_intel_10<R>(); }

} // namespace ConcuBinE::test
