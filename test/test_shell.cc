#include <gtest/gtest.h>

#include "shell.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct Shell_Test : public ::testing::Test
{
  Shell shell;
};

/* return_code ****************************************************************/
TEST_F(Shell_Test, return_code)
{
  shell.run("exit 0");
  ASSERT_EQ(0, shell.last_exit_code());

  shell.run("exit 1");
  ASSERT_EQ(1, shell.last_exit_code());

  shell.run("exit -1");
  ASSERT_EQ(255, shell.last_exit_code());
}

/* output *********************************************************************/
TEST_F(Shell_Test, ouput)
{
  string expected = "hello shell";

  string actual = shell.run("echo -n " + expected).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* input_output ***************************************************************/
TEST_F(Shell_Test, input_output)
{
  string expected = "hello shell";

  string actual = shell.run("cat", expected).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* pipe_in_pipe ***************************************************************/
TEST_F(Shell_Test, pipe_in_pipe)
{
  string input = "3\n2\n4\n5\n1\n3\n2\n4\n5\n1\n";
  string expected = "1\n2\n3\n4\n5\n";

  string actual = shell.run("sort | uniq", input).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* abuse **********************************************************************/
TEST_F(Shell_Test, abuse)
{
  string expected = "bash: unknown: command not found\n";
  string actual = shell.run("unknown").str();

  ASSERT_EQ(127, shell.last_exit_code());
  ASSERT_EQ(expected, actual);

  actual = shell.run("").str();
  ASSERT_EQ("", actual);

  string input;
  actual= shell.run("echo ", input).str();
  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ("\n", actual);
}
