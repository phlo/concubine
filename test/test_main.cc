#include <gtest/gtest.h>

#include <fstream>

#include "shell.hh"

namespace test {

//==============================================================================
// Main tests
//==============================================================================

struct Main : public ::testing::Test
{
  std::string executable = "../concubine";

  Shell shell;
};

// illegal command line ========================================================

TEST_F(Main, illegal_command_line)
{
  std::string cmd = executable;

  std::string actual = shell.run(cmd + " WRONG").str();

  ASSERT_EQ(255, shell.last_exit_code());

  std::string expected = "error: no command given";

  actual = shell.run(cmd + " help").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: unknown command WRONG";

  actual = shell.run(cmd + " help WRONG").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

// simulate ====================================================================

TEST_F(Main, simulate_increment_check)
{
  // read expected schedule from file
  std::ifstream schedule_file("data/increment.check.t2.k16.schedule");
  std::string expected((std::istreambuf_iterator<char>(schedule_file)),
                        std::istreambuf_iterator<char>());

  std::string args = " simulate -v -s 0 -k 16 ";
  std::string increment_0 = " data/increment.check.thread.0.asm ";
  std::string increment_n = " data/increment.check.thread.n.asm ";
  std::string cmd = executable + args + increment_0 + " " + increment_n;

  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, simulate_increment_cas)
{
  // read expected schedule from file
  std::ifstream schedule_file("data/increment.cas.t2.k16.schedule");
  std::string expected((std::istreambuf_iterator<char>(schedule_file)),
                        std::istreambuf_iterator<char>());

  std::string args = " simulate -v -s 0 -k 16 ";
  std::string increment = "data/increment.cas.asm";
  std::string cmd = executable + args + increment + " " + increment;

  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, simulate_missing_args)
{
  std::string args = " simulate";

  std::string expected = "error: got nothing to run\n";
  std::string actual = shell.run(executable + args).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  actual = shell.run(executable + args + " -v").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing seed\n";

  actual = shell.run(executable + args + " -s").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing bound\n";

  actual = shell.run(executable + args + " -k").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, simulate_file_not_found)
{
  std::string args = " simulate ";
  std::string program_file = "file_not_found";
  std::string cmd = executable + args + program_file;

  std::string actual = shell.run(cmd).str();
  std::string expected = "error: " + program_file + " not found\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, simulate_illegal_seed)
{
  std::string args = " simulate -s WRONG ";
  std::string cmd = executable + args + "none.asm";

  std::string actual = shell.run(cmd).str();
  std::string expected = "error: illegal seed [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, simulate_illegal_bound)
{
  std::string args = " simulate -k WRONG ";
  std::string cmd = executable + args + "none.asm";

  std::string actual = shell.run(cmd).str();
  std::string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

// replay ======================================================================

TEST_F(Main, replay_increment_check)
{
  std::string schedule_file = "data/increment.check.t2.k16.schedule";

  // read expected schedule from file
  std::ifstream sfs(schedule_file);
  std::string expected((std::istreambuf_iterator<char>(sfs)),
                        std::istreambuf_iterator<char>());

  std::string args = " replay -v ";
  std::string cmd = executable + args + schedule_file;

  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, replay_increment_cas)
{
  std::string schedule_file = "data/increment.cas.t2.k16.schedule";

  // read expected schedule from file
  std::ifstream sfs(schedule_file);
  std::string expected((std::istreambuf_iterator<char>(sfs)),
                        std::istreambuf_iterator<char>());

  std::string args = " replay -v ";
  std::string cmd = executable + args + schedule_file;

  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, replay_missing_args)
{
  std::string args = " replay";

  std::string expected = "error: no schedule given\n";
  std::string actual = shell.run(executable + args).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  actual = shell.run(executable + args + " -v").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing bound\n";

  actual = shell.run(executable + args + " -k").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, replay_file_not_found)
{
  std::string args = " replay ";
  std::string program_file = "file_not_found";
  std::string cmd = executable + args + program_file;

  std::string actual = shell.run(cmd).str();
  std::string expected = "error: " + program_file + " not found\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, replay_illegal_bound)
{
  std::string args = " replay -k WRONG ";
  std::string cmd = executable + args + "none.asm";

  std::string actual = shell.run(cmd).str();
  std::string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

// solve =======================================================================

TEST_F(Main, solve_pretend_functional_cas)
{
  std::string args = " solve -v -p 12 ";
  std::string program_file = "data/increment.cas.asm";

  std::string cmd = executable + args + program_file + " " + program_file;

  // read expected smt formula from file
  std::ifstream ffs("data/increment.cas.functional.t2.k12.smt2");
  std::string expected((std::istreambuf_iterator<char>(ffs)),
                        std::istreambuf_iterator<char>());

  std::string actual = shell.run(cmd).str();

  EXPECT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected + '\n', actual);
}

TEST_F(Main, solve_cas)
{
  std::string args = " solve -v 8 ";
  std::string program = "data/increment.cas.asm";
  std::string cmd = executable + args + program + " " + program;

  std::string expected = "sat";
  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ("", actual);
}

TEST_F(Main, solve_illegal_args)
{
  executable = executable + " solve ";
  std::string program = "data/increment.cas.asm";

  // no arguments
  std::string expected = "error: too few arguments\n";
  std::string actual = shell.run(executable).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // unknown option
  expected = "error: unknown option [-foo]\n";
  actual = shell.run(executable + "-foo 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // missing bound
  expected = "error: illegal bound [" + program + "]\n";
  actual = shell.run(executable + program + " " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // illegal bound (std::string)
  expected = "error: illegal bound [WRONG]\n";
  actual = shell.run(executable + "WRONG " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // illegal bound (0)
  expected = "error: illegal bound [0]\n";
  actual = shell.run(executable + "0 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // constraint file missing
  expected = "error: 1 not found\n";
  actual = shell.run(executable + "-c 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing constraints file\n";
  actual = shell.run(executable + "-v -c").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // constraint file not found
  expected = "error: FILE not found\n";
  actual = shell.run(executable + "-c FILE 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // encoder missing
  expected = "error: missing encoder\n";
  actual = shell.run(executable + "-v -e").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // unknown encoder
  expected = "error: unknown encoder [FOO]\n";
  actual = shell.run(executable + "-e FOO 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // unknown solver
  expected = "error: unknown solver [FOO]\n";
  actual = shell.run(executable + "-s FOO 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_file_not_found)
{
  std::string args = " solve 1 ";
  std::string cmd = executable + args;

  std::string expected = "error: file_not_found not found\n";
  std::string actual = shell.run(cmd + "file_not_found").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);

  actual = shell.run(cmd + "data/increment.cas.asm file_not_found").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

} // namespace test
