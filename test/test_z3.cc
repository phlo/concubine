/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

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
TEST_F(Z3, simulate_check_functional) { simulate_check<F>(); }
TEST_F(Z3, simulate_check_relational) { simulate_check<R>(); }

TEST_F(Z3, simulate_cas_functional) { simulate_cas<F>(); }
TEST_F(Z3, simulate_cas_relational) { simulate_cas<R>(); }

TEST_F(Z3, simulate_indirect_functional) { simulate_indirect<F>(); }
TEST_F(Z3, simulate_indirect_relational) { simulate_indirect<R>(); }

TEST_F(Z3, simulate_halt_functional) { simulate_halt<F>(); }
TEST_F(Z3, simulate_halt_relational) { simulate_halt<R>(); }

// feature tests
//
TEST_F(Z3, verify_indirect_functional) { verify_indirect<F>(); }
TEST_F(Z3, verify_indirect_relational) { verify_indirect<R>(); }

TEST_F(Z3, verify_halt_functional) { verify_halt<F>(); }
TEST_F(Z3, verify_halt_relational) { verify_halt<R>(); }

// demo example tests
//
TEST_F(Z3, demo_functional) { demo<F>(); }
TEST_F(Z3, demo_relational) { demo<R>(); }

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

TEST_F(Z3, litmus_intel_8_functional) { litmus_intel_8<F>(); }
TEST_F(Z3, litmus_intel_8_relational) { litmus_intel_8<R>(); }

TEST_F(Z3, litmus_intel_9_functional) { litmus_intel_9<F>(); }
TEST_F(Z3, litmus_intel_9_relational) { litmus_intel_9<R>(); }

TEST_F(Z3, litmus_intel_10_functional) { litmus_intel_10<F>(); }
TEST_F(Z3, litmus_intel_10_relational) { litmus_intel_10<R>(); }

TEST_F(Z3, litmus_amd_1_functional) { litmus_amd_1<F>(); }
TEST_F(Z3, litmus_amd_1_relational) { litmus_amd_1<R>(); }

TEST_F(Z3, litmus_amd_2_functional) { litmus_amd_2<F>(); }
TEST_F(Z3, litmus_amd_2_relational) { litmus_amd_2<R>(); }

TEST_F(Z3, litmus_amd_3_functional) { litmus_amd_3<F>(); }
TEST_F(Z3, litmus_amd_3_relational) { litmus_amd_3<R>(); }

TEST_F(Z3, litmus_amd_4_functional) { litmus_amd_4<F>(); }
TEST_F(Z3, litmus_amd_4_relational) { litmus_amd_4<R>(); }

TEST_F(Z3, litmus_amd_5_functional) { litmus_amd_5<F>(); }
TEST_F(Z3, litmus_amd_5_relational) { litmus_amd_5<R>(); }

TEST_F(Z3, litmus_amd_6_functional) { litmus_amd_6<F>(); }
TEST_F(Z3, litmus_amd_6_relational) { litmus_amd_6<R>(); }

TEST_F(Z3, litmus_amd_7_functional) { litmus_amd_7<F>(); }
TEST_F(Z3, litmus_amd_7_relational) { litmus_amd_7<R>(); }

TEST_F(Z3, litmus_amd_8_functional) { litmus_amd_8<F>(); }
TEST_F(Z3, litmus_amd_8_relational) { litmus_amd_8<R>(); }

TEST_F(Z3, litmus_amd_9_functional) { litmus_amd_9<F>(); }
TEST_F(Z3, litmus_amd_9_relational) { litmus_amd_9<R>(); }

} // namespace ConcuBinE::test
