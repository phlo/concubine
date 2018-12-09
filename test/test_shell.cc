#include <gtest/gtest.h>

#include "shell.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ShellTest : public ::testing::Test
{
  Shell shell;
};

/* return_code ****************************************************************/
TEST_F(ShellTest, return_code)
{
  shell.run("exit 0");
  ASSERT_EQ(0, shell.last_exit_code());

  shell.run("exit 1");
  ASSERT_EQ(1, shell.last_exit_code());

  shell.run("exit -1");
  ASSERT_EQ(255, shell.last_exit_code());
}

/* output *********************************************************************/
TEST_F(ShellTest, ouput)
{
  string expected = "hello shell";

  string actual = shell.run("echo -n " + expected);

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* input_output ***************************************************************/
TEST_F(ShellTest, input_output)
{
  string expected = "hello shell";

  string actual = shell.run("cat", expected);

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* pipe_in_pipe ***************************************************************/
TEST_F(ShellTest, pipe_in_pipe)
{
  string input = "3\n2\n4\n5\n1\n3\n2\n4\n5\n1\n";
  string expected = "1\n2\n3\n4\n5\n";

  string actual = shell.run("sort | uniq", input);

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* abuse **********************************************************************/
TEST_F(ShellTest, abuse)
{
  string expected = "bash: unknown: command not found\n";
  string actual = shell.run("unknown");

  ASSERT_EQ(127, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());

  actual = shell.run("");
  ASSERT_STREQ("", actual.c_str());

  string input;
  actual= shell.run("echo ", input);
  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ("\n", actual.c_str());
}
