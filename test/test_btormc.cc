#include "test_solver.hh"

#include "btormc.hh"

namespace ConcuBinE::test {

//==============================================================================
// BtorMC tests
//==============================================================================

using BtorMC = Solver<BtorMC>;

// BtorMC::sat =================================================================

TEST_F(BtorMC, sat)
{
  ASSERT_TRUE(solver.sat(
    "1 sort bitvec 1\n"
    "2 state 1 x\n"
    "3 bad 2\n"));
  ASSERT_EQ(
    "sat\n"
    "b0 \n"
    "#0\n"
    "0 1 x#0\n"
    "@0\n"
    ".\n",
    solver.std_out.str());
}

TEST_F(BtorMC, unsat)
{
  ASSERT_FALSE(solver.sat(
    "1 sort bitvec 1\n"
    "2 state 1 x\n"));
  ASSERT_EQ("", solver.std_out.str());
}

// BtorMC::solve ===============================================================

using E = btor2::Encoder;

// simulation tests
//
TEST_F(BtorMC, simulate_check) { simulate_check<E>(); }
TEST_F(BtorMC, simulate_cas) { simulate_cas<E>(); }
TEST_F(BtorMC, simulate_indirect) { simulate_indirect<E>(); }
TEST_F(BtorMC, simulate_halt) { simulate_halt<E>(); }

// feature tests
//
TEST_F(BtorMC, verify_indirect_functional) { verify_indirect<E>(); }

// litmus tests
//
TEST_F(BtorMC, litmus_intel_1) { litmus_intel_1<E>(); }
TEST_F(BtorMC, litmus_intel_2) { litmus_intel_2<E>(); }
TEST_F(BtorMC, litmus_intel_3) { litmus_intel_3<E>(); }
TEST_F(BtorMC, litmus_intel_4) { litmus_intel_4<E>(); }
TEST_F(BtorMC, litmus_intel_5) { litmus_intel_5<E>(); }
TEST_F(BtorMC, litmus_intel_6) { litmus_intel_6<E>(); }
TEST_F(BtorMC, litmus_intel_7) { litmus_intel_7<E>(); }
TEST_F(BtorMC, litmus_intel_8) { litmus_intel_8<E>(); }
TEST_F(BtorMC, litmus_intel_9) { litmus_intel_9<E>(); }
TEST_F(BtorMC, litmus_intel_10) { litmus_intel_10<E>(); }

TEST_F(BtorMC, litmus_amd_1) { litmus_amd_1<E>(); }
TEST_F(BtorMC, litmus_amd_2) { litmus_amd_2<E>(); }
TEST_F(BtorMC, litmus_amd_3) { litmus_amd_3<E>(); }
TEST_F(BtorMC, litmus_amd_4) { litmus_amd_4<E>(); }
TEST_F(BtorMC, litmus_amd_5) { litmus_amd_5<E>(); }
TEST_F(BtorMC, litmus_amd_6) { litmus_amd_6<E>(); }

} // namespace ConcuBinE::test
