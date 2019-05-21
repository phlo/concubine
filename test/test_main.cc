#include <gtest/gtest.h>

#include <fstream>

#include "shell.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct MainTest : public ::testing::Test
{
  Shell shell;

  /* executable file name */
  string executable = "../concubine";
};

/* illegal_commands ***********************************************************/
TEST_F(MainTest, illegal_commands)
{
  string cmd = executable;

  string actual = shell.run(cmd + " WRONG").str();

  ASSERT_EQ(255, shell.last_exit_code());

  string expected = "error: no command given";

  actual = shell.run(cmd + " help").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: unknown command WRONG";

  actual = shell.run(cmd + " help WRONG").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

/* simulate_increment_check ***************************************************/
TEST_F(MainTest, simulate_increment_check)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.check.t2.k16.schedule");
  string expected((istreambuf_iterator<char>(schedule_file)),
                   istreambuf_iterator<char>());

  string args = " simulate -v -s 0 -k 16 ";
  string increment_0 = " data/increment.check.thread.0.asm ";
  string increment_n = " data/increment.check.thread.n.asm ";

  string cmd = executable + args + increment_0 + " " + increment_n;

  string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* simulate_increment_cas *****************************************************/
TEST_F(MainTest, simulate_increment_cas)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.cas.t2.k16.schedule");
  string expected((istreambuf_iterator<char>(schedule_file)),
                   istreambuf_iterator<char>());

  string args = " simulate -v -s 0 -k 16 ";
  string increment = "data/increment.cas.asm";

  string cmd = executable + args + increment + " " + increment;

  string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* simulate_missing_args ******************************************************/
TEST_F(MainTest, simulate_missing_args)
{
  string args = " simulate";

  string expected = "error: got nothing to run\n";

  string actual = shell.run(executable + args).str();

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

/* simulate_file_not_found ****************************************************/
TEST_F(MainTest, simulate_file_not_found)
{
  string args = " simulate ";

  string program_file = "file_not_found";

  string cmd = executable + args + program_file;

  string actual = shell.run(cmd).str();

  string expected = "error: " + program_file + " not found\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* simulate_illegal_seed ******************************************************/
TEST_F(MainTest, simulate_illegal_seed)
{
  string args = " simulate -s WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd).str();

  string expected = "error: illegal seed [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* simulate_illegal_bound *****************************************************/
TEST_F(MainTest, simulate_illegal_bound)
{
  string args = " simulate -k WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd).str();

  string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* replay_increment_check *****************************************************/
TEST_F(MainTest, replay_increment_check)
{
  string schedule_file = "data/increment.check.t2.k16.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string expected((istreambuf_iterator<char>(sfs)),
                   istreambuf_iterator<char>());

  string args = " replay -v ";

  string cmd = executable + args + schedule_file;

  string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* replay_increment_cas *******************************************************/
TEST_F(MainTest, replay_increment_cas)
{
  string schedule_file = "data/increment.cas.t2.k16.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string expected((istreambuf_iterator<char>(sfs)),
                   istreambuf_iterator<char>());

  string args = " replay -v ";

  string cmd = executable + args + schedule_file;

  string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* replay_missing_args ********************************************************/
TEST_F(MainTest, replay_missing_args)
{
  string args = " replay";

  string expected = "error: no schedule given\n";

  string actual = shell.run(executable + args).str();

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

/* replay_file_not_found ******************************************************/
TEST_F(MainTest, replay_file_not_found)
{
  string args = " replay ";

  string program_file = "file_not_found";

  string cmd = executable + args + program_file;

  string actual = shell.run(cmd).str();

  string expected = "error: " + program_file + " not found\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* replay_illegal_bound *******************************************************/
TEST_F(MainTest, replay_illegal_bound)
{
  string args = " replay -k WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd).str();

  string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

/* solve_pretend_functional_cas ***********************************************/
TEST_F(MainTest, solve_pretend_functional_cas)
{
  string args = " solve -v -p 12 ";
  string program_file = "data/increment.cas.asm";

  string cmd = executable + args + program_file + " " + program_file;

  /* read expected smt formula from file */
  ifstream ffs("data/increment.cas.functional.t2.k12.smt2");
  string expected((istreambuf_iterator<char>(ffs)),
                   istreambuf_iterator<char>());

  string actual = shell.run(cmd).str();

  EXPECT_EQ(0, shell.last_exit_code());
  ASSERT_EQ(expected + '\n', actual);
}

/* solve_cas ******************************************************************/
TEST_F(MainTest, solve_cas)
{
  string args = " solve -v 8 ";
  string program = "data/increment.cas.asm";

  string cmd = executable + args + program + " " + program;

  string expected = "sat";

  string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ("", actual);
}

/* solve_illegal_args *********************************************************/
TEST_F(MainTest, solve_illegal_args)
{
  executable = executable + " solve ";
  string program = "data/increment.cas.asm";

  /* no arguments */
  string expected = "error: too few arguments\n";

  string actual = shell.run(executable).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* unknown option */
  expected = "error: unknown option [-foo]\n";

  actual = shell.run(executable + "-foo 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* missing bound */
  expected = "error: illegal bound [" + program + "]\n";

  actual = shell.run(executable + program + " " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* illegal bound (string) */
  expected = "error: illegal bound [WRONG]\n";

  actual = shell.run(executable + "WRONG " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* illegal bound (0) */
  expected = "error: illegal bound [0]\n";

  actual = shell.run(executable + "0 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* constraint file missing */
  expected = "error: 1 not found\n";

  actual = shell.run(executable + "-c 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing constraints file\n";

  actual = shell.run(executable + "-v -c").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* constraint file not found */
  expected = "error: FILE not found\n";

  actual = shell.run(executable + "-c FILE 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* encoder missing */
  expected = "error: missing encoder\n";

  actual = shell.run(executable + "-v -e").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* unknown encoder */
  expected = "error: unknown encoder [FOO]\n";

  actual = shell.run(executable + "-e FOO 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* unknown solver */
  expected = "error: unknown solver [FOO]\n";

  actual = shell.run(executable + "-s FOO 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

/* solve_file_not_found *******************************************************/
TEST_F(MainTest, solve_file_not_found)
{
  string args = " solve 1 ";
  string cmd = executable + args;

  string expected = "error: file_not_found not found\n";

  string actual = shell.run(cmd + "file_not_found").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);

  actual = shell.run(cmd + "data/increment.cas.asm file_not_found").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}
