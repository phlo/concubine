#include <gtest/gtest.h>

#include <sstream>

#include "encoder.hh"
#include "verifier.hh"
#include "boolector.hh"
#include "streamredirecter.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct VerifierTest : public ::testing::Test
{
  Boolector       boolector;
  Program         program;
  smtlib::Encoder encoder;
  string          specification;
  Verifier        verifier;

  VerifierTest () :
    encoder(program, 0),
    verifier(boolector, encoder, specification) {}
};

/* sat ************************************************************************/
TEST_F(VerifierTest, sat)
{
  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(verifier.sat());

  redirecter.stop();

  ASSERT_STREQ("sat\n", ss.str().c_str());
}
