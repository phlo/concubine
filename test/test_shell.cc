#include <gtest/gtest.h>

#include "shell.hh"

namespace ConcuBinE::test {

//==============================================================================
// Shell tests
//==============================================================================

struct Shell : public ::testing::Test
{
  ConcuBinE::Shell shell;
};

// Shell::last_exit_code =======================================================

TEST_F(Shell, return_code)
{
  shell.run("exit 0");
  ASSERT_EQ(0, shell.last_exit_code());

  shell.run("exit 1");
  ASSERT_EQ(1, shell.last_exit_code());

  shell.run("exit -1");
  ASSERT_EQ(255, shell.last_exit_code());
}

// Shell::run ==================================================================

TEST_F(Shell, ouput)
{
  std::string expected = "hello shell";

  std::string actual = shell.run("echo -n " + expected).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Shell, input_output)
{
  std::string expected = "hello shell";

  std::string actual = shell.run("cat", expected).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Shell, pipe_in_pipe)
{
  std::string input = "3\n2\n4\n5\n1\n3\n2\n4\n5\n1\n";
  std::string expected = "1\n2\n3\n4\n5\n";

  std::string actual = shell.run("sort | uniq", input).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Shell, abuse)
{
  std::string expected = "bash: unknown: command not found\n";
  std::string actual = shell.run("unknown").str();

  ASSERT_EQ(127, shell.last_exit_code());
  ASSERT_EQ(expected, actual);

  actual = shell.run("").str();
  ASSERT_EQ("", actual);

  std::string input;
  actual= shell.run("echo ", input).str();
  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ("\n", actual);
}

} // namespace ConcuBinE::test
