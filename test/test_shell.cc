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

/* ReturnCode *****************************************************************/
TEST_F(ShellTest, ReturnCode)
{
  shell.run("exit 0");
  ASSERT_EQ(0, shell.lastExitCode());

  shell.run("exit 1");
  ASSERT_EQ(1, shell.lastExitCode());

  shell.run("exit -1");
  ASSERT_EQ(255, shell.lastExitCode());
}

/* Output *********************************************************************/
TEST_F(ShellTest, Ouput)
{
  string expectedOutput = "hello shell";

  string actualOutput = shell.run("echo -n " + expectedOutput);

  ASSERT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ(expectedOutput.c_str(), actualOutput.c_str());
}

/* InputOutput ****************************************************************/
TEST_F(ShellTest, InputOutput)
{
  string input = "hello shell";
  string expectedOutput = input;

  string actualOutput = shell.run("cat", input);

  ASSERT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ(expectedOutput.c_str(), actualOutput.c_str());
}

/* PipeInPipe *****************************************************************/
TEST_F(ShellTest, PipeInPipe)
{
  string input = "3\n2\n4\n5\n1\n3\n2\n4\n5\n1\n";
  string expectedOutput = "1\n2\n3\n4\n5\n";

  string actualOutput = shell.run("sort | uniq", input);

  ASSERT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ(expectedOutput.c_str(), actualOutput.c_str());
}

/* Abuse **********************************************************************/
TEST_F(ShellTest, Abuse)
{
  string expectedOutput = "bash: unknown: command not found\n";
  string actualOutput = shell.run("unknown");

  ASSERT_EQ(127, shell.lastExitCode());
  ASSERT_STREQ(expectedOutput.c_str(), actualOutput.c_str());

  actualOutput = shell.run("");
  ASSERT_STREQ("", actualOutput.c_str());

  string input;
  actualOutput = shell.run("echo ", input);
  ASSERT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ("\n", actualOutput.c_str());
}
