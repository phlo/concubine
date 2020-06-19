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
  ASSERT_EQ("sat\n", solver.stdout.str());
}

TEST_F(CVC4, unsat)
{
  ASSERT_FALSE(solver.sat("(set-logic QF_AUFBV)(assert false)(check-sat)"));
  ASSERT_EQ("unsat\n", solver.stdout.str());
}

// CVC4::solve =================================================================

using F = smtlib::Functional;
using R = smtlib::Relational;

// simulation tests
//
TEST_F(CVC4, simulate_check_functional) { simulate_check<F>(); }
TEST_F(CVC4, simulate_check_relational) { simulate_check<R>(); }

TEST_F(CVC4, simulate_cas_functional) { simulate_cas<F>(); }
TEST_F(CVC4, simulate_cas_relational) { simulate_cas<R>(); }

TEST_F(CVC4, simulate_indirect_functional) { simulate_indirect<F>(); }
TEST_F(CVC4, simulate_indirect_relational) { simulate_indirect<R>(); }

TEST_F(CVC4, simulate_halt_functional) { simulate_halt<F>(); }
TEST_F(CVC4, simulate_halt_relational) { simulate_halt<R>(); }

// feature tests
//
TEST_F(CVC4, verify_indirect_functional) { verify_indirect<F>(); }
TEST_F(CVC4, verify_indirect_relational) { verify_indirect<R>(); }

TEST_F(CVC4, verify_halt_functional) { verify_halt<F>(); }
TEST_F(CVC4, verify_halt_relational) { verify_halt<R>(); }

// demo example tests
//
TEST_F(CVC4, DISABLED_demo_functional) { demo<F>(); }
TEST_F(CVC4, DISABLED_demo_relational) { demo<R>(); }

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

TEST_F(CVC4, DISABLED_litmus_intel_5_functional) { litmus_intel_5<F>(); } // 18s
TEST_F(CVC4, litmus_intel_5_relational) { litmus_intel_5<R>(); }

TEST_F(CVC4, litmus_intel_6_functional) { litmus_intel_6<F>(); }
TEST_F(CVC4, litmus_intel_6_relational) { litmus_intel_6<R>(); }

TEST_F(CVC4, DISABLED_litmus_intel_7_functional) { litmus_intel_7<F>(); } // 1h 21m 54s
TEST_F(CVC4, DISABLED_litmus_intel_7_relational) { litmus_intel_7<R>(); } // 8h 56m 35s

TEST_F(CVC4, DISABLED_litmus_intel_8_functional) { litmus_intel_8<F>(); } // 4m 38s
TEST_F(CVC4, DISABLED_litmus_intel_8_relational) { litmus_intel_8<R>(); } // 4h 50m 10s

TEST_F(CVC4, litmus_intel_9_functional) { litmus_intel_9<F>(); }
TEST_F(CVC4, litmus_intel_9_relational) { litmus_intel_9<R>(); }

TEST_F(CVC4, litmus_intel_10_functional) { litmus_intel_10<F>(); }
TEST_F(CVC4, litmus_intel_10_relational) { litmus_intel_10<R>(); }

TEST_F(CVC4, litmus_amd_1_functional) { litmus_amd_1<F>(); }
TEST_F(CVC4, litmus_amd_1_relational) { litmus_amd_1<R>(); }

TEST_F(CVC4, litmus_amd_2_functional) { litmus_amd_2<F>(); }
TEST_F(CVC4, litmus_amd_2_relational) { litmus_amd_2<R>(); }

TEST_F(CVC4, litmus_amd_3_functional) { litmus_amd_3<F>(); }
TEST_F(CVC4, litmus_amd_3_relational) { litmus_amd_3<R>(); }

TEST_F(CVC4, litmus_amd_4_functional) { litmus_amd_4<F>(); }
TEST_F(CVC4, litmus_amd_4_relational) { litmus_amd_4<R>(); }

TEST_F(CVC4, litmus_amd_5_functional) { litmus_amd_5<F>(); }
TEST_F(CVC4, DISABLED_litmus_amd_5_relational) { litmus_amd_5<R>(); } // 24s

TEST_F(CVC4, DISABLED_litmus_amd_6_functional) { litmus_amd_6<F>(); } // 1h 20m 52s
TEST_F(CVC4, DISABLED_litmus_amd_6_relational) { litmus_amd_6<R>(); } // 8h 56m 35s

TEST_F(CVC4, litmus_amd_7_functional) { litmus_amd_7<F>(); }
TEST_F(CVC4, litmus_amd_7_relational) { litmus_amd_7<R>(); }

TEST_F(CVC4, DISABLED_litmus_amd_8_functional) { litmus_amd_8<F>(); } // 1m 15s
TEST_F(CVC4, litmus_amd_8_relational) { litmus_amd_8<R>(); }

TEST_F(CVC4, litmus_amd_9_functional) { litmus_amd_9<F>(); }
TEST_F(CVC4, DISABLED_litmus_amd_9_relational) { litmus_amd_9<R>(); } // 27m 44s

} // namespace ConcuBinE::test
