#include <gtest/gtest.h>

#include "shell.hh"

namespace ConcuBinE::test {

//==============================================================================
// Shell tests
//==============================================================================

// Shell::run ==================================================================

TEST(Shell, exit)
{
  ASSERT_EQ(0, shell::run({"bash"}, "exit 0").exit);
  ASSERT_EQ(1, shell::run({"bash"}, "exit 1").exit);
  ASSERT_EQ(255, shell::run({"bash"}, "exit -1").exit);
}

TEST(Shell, stdout)
{
  const std::string expected = "hello world";
  const auto out = shell::run({"echo", "-n", expected});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ(expected, out.stdout.str());
  ASSERT_EQ("", out.stderr.str());
}

TEST(Shell, stderr)
{
  const std::string expected = "hello world";
  const auto out = shell::run({"bash"}, "echo " + expected + " 1>&2");

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());
  ASSERT_EQ(expected + '\n', out.stderr.str());
}

TEST(Shell, input)
{
  const std::string expected = "hello world";
  const auto out = shell::run({"cat"}, expected);

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ(expected, out.stdout.str());
  ASSERT_EQ("", out.stderr.str());
}

TEST(Shell, abuse)
{
  const char * expected = "error calling exec [No such file or directory]";

  try { shell::run({"unknown"}); }
  catch (const std::exception & e) { ASSERT_STREQ(expected, e.what()); }

  try { shell::run({""}); }
  catch (const std::exception & e) { ASSERT_STREQ(expected, e.what()); }
}

} // namespace ConcuBinE::test
