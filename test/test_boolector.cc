#include "test_solver.hh"

#include "boolector.hh"

namespace ConcuBinE::test {

//==============================================================================
// Boolector tests
//==============================================================================

using Boolector = Solver<Boolector>;

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

using F = smtlib::Functional;
using R = smtlib::Relational;

// simulation tests
//
TEST_F(Boolector, simulate_check_functional) { simulate_check<F>(); }
TEST_F(Boolector, simulate_check_relational) { simulate_check<R>(); }

TEST_F(Boolector, simulate_cas_functional) { simulate_cas<F>(); }
TEST_F(Boolector, simulate_cas_relational) { simulate_cas<R>(); }

TEST_F(Boolector, simulate_indirect_functional) { simulate_indirect<F>(); }
TEST_F(Boolector, simulate_indirect_relational) { simulate_indirect<R>(); }

TEST_F(Boolector, simulate_halt_functional) { simulate_halt<F>(); }
TEST_F(Boolector, simulate_halt_relational) { simulate_halt<R>(); }

// feature tests
//
TEST_F(Boolector, verify_indirect_functional) { verify_indirect<F>(); }
TEST_F(Boolector, verify_indirect_relational) { verify_indirect<R>(); }

// litmus tests
//
TEST_F(Boolector, litmus_intel_1_functional) { litmus_intel_1<F>(); }
TEST_F(Boolector, litmus_intel_1_relational) { litmus_intel_1<R>(); }

TEST_F(Boolector, litmus_intel_2_functional) { litmus_intel_2<F>(); }
TEST_F(Boolector, litmus_intel_2_relational) { litmus_intel_2<R>(); }

TEST_F(Boolector, litmus_intel_3_functional) { litmus_intel_3<F>(); }
TEST_F(Boolector, litmus_intel_3_relational) { litmus_intel_3<R>(); }

TEST_F(Boolector, litmus_intel_4_functional) { litmus_intel_4<F>(); }
TEST_F(Boolector, litmus_intel_4_relational) { litmus_intel_4<R>(); }

TEST_F(Boolector, litmus_intel_5_functional) { litmus_intel_5<F>(); }
TEST_F(Boolector, litmus_intel_5_relational) { litmus_intel_5<R>(); }

TEST_F(Boolector, litmus_intel_6_functional) { litmus_intel_6<F>(); }
TEST_F(Boolector, litmus_intel_6_relational) { litmus_intel_6<R>(); }

TEST_F(Boolector, litmus_intel_7_functional) { litmus_intel_7<F>(); }
TEST_F(Boolector, litmus_intel_7_relational) { litmus_intel_7<R>(); }

TEST_F(Boolector, litmus_intel_8_functional) { litmus_intel_8<F>(); }
TEST_F(Boolector, litmus_intel_8_relational) { litmus_intel_8<R>(); }

TEST_F(Boolector, litmus_intel_9_functional) { litmus_intel_9<F>(); }
TEST_F(Boolector, litmus_intel_9_relational) { litmus_intel_9<R>(); }

TEST_F(Boolector, litmus_intel_10_functional) { litmus_intel_10<F>(); }
TEST_F(Boolector, litmus_intel_10_relational) { litmus_intel_10<R>(); }

TEST_F(Boolector, litmus_amd_1_functional) { litmus_amd_1<F>(); }
TEST_F(Boolector, litmus_amd_1_relational) { litmus_amd_1<R>(); }

TEST_F(Boolector, litmus_amd_2_functional) { litmus_amd_2<F>(); }
TEST_F(Boolector, litmus_amd_2_relational) { litmus_amd_2<R>(); }

TEST_F(Boolector, litmus_amd_3_functional) { litmus_amd_3<F>(); }
TEST_F(Boolector, litmus_amd_3_relational) { litmus_amd_3<R>(); }

TEST_F(Boolector, litmus_amd_4_functional) { litmus_amd_4<F>(); }
TEST_F(Boolector, litmus_amd_4_relational) { litmus_amd_4<R>(); }

TEST_F(Boolector, litmus_amd_5_functional) { litmus_amd_5<F>(); }
TEST_F(Boolector, litmus_amd_5_relational) { litmus_amd_5<R>(); }

TEST_F(Boolector, litmus_amd_6_functional) { litmus_amd_6<F>(); }
TEST_F(Boolector, litmus_amd_6_relational) { litmus_amd_6<R>(); }

TEST_F(Boolector, litmus_amd_7_functional) { litmus_amd_7<F>(); }
TEST_F(Boolector, litmus_amd_7_relational) { litmus_amd_7<R>(); }

TEST_F(Boolector, litmus_amd_8_functional) { litmus_amd_8<F>(); }
TEST_F(Boolector, litmus_amd_8_relational) { litmus_amd_8<R>(); }

} // namespace ConcuBinE::test
