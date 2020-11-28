/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include <gtest/gtest.h>

//==============================================================================
// global variables
//==============================================================================

namespace ConcuBinE {

bool verbose = true;
uint64_t seed = 0;
namespace btor2 { long expressions = 0; }
namespace smtlib { long expressions = 0; }

} // namespace ConcuBinE

//==============================================================================
// main
//==============================================================================

int main (int argc, char ** argv)
{
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
