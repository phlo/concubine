#include <gtest/gtest.h>

#include <ostream>
#include <iostream>

/* externals ******************************************************************/
bool verbose = true;

/*******************************************************************************
 * main
*******************************************************************************/
int main (int argc, char ** argv)
{
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
