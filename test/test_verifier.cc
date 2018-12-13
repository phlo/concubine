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
  ProgramListPtr  programs;
  EncoderPtr      encoder;
  string          specification;
  Verifier        verifier;

  VerifierTest () :
    programs(nullptr),
    encoder(nullptr),
    verifier(boolector, *encoder, specification) {}
};

#ifdef __NIGNORE__
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
#endif
