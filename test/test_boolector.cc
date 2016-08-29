#include <gtest/gtest.h>

#include <sstream>

#include "boolector.hh"
#include "streamredirecter.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct BoolectorTest : public ::testing::Test
{
  Boolector boolector;
};

/* sat ************************************************************************/
TEST_F(BoolectorTest, sat)
{
  string formula = "(exit)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_STREQ("sat\n", ss.str().c_str());
}
