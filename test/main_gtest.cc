#include <gtest/gtest.h>

//==============================================================================
// global variables
//==============================================================================

namespace ConcuBinE {

bool verbose = true;

} // namespace ConcuBinE

//==============================================================================
// main
//==============================================================================

int main (int argc, char ** argv)
{
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
