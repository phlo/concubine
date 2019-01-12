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
  string executable = "../psimsmt";
};

/* illegal_commands ***********************************************************/
TEST_F(MainTest, illegal_commands)
{
  string cmd = executable;

  string actual = shell.run(cmd + " WRONG");

  ASSERT_EQ(255, shell.last_exit_code());

  string expected = "error: no command given";

  actual = shell.run(cmd + " help");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: unknown command WRONG";

  actual = shell.run(cmd + " help WRONG");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());
}

/* simulate_increment_0 *******************************************************/
TEST_F(MainTest, simulate_increment_0)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.invalid.schedule");
  string expected(( istreambuf_iterator<char>(schedule_file) ),
                    istreambuf_iterator<char>());

  string args           = " simulate -v -s 0 ";
  string checker_file   = " data/increment.checker.asm ";
  string increment_file = " data/increment.asm ";

  string cmd =
    executable + args + checker_file + increment_file + increment_file;

  string actual = shell.run(cmd);

  ASSERT_EQ(1, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulate_increment_cas *****************************************************/
TEST_F(MainTest, simulate_increment_cas)
{
  /* read expected schedule from file */
  ifstream schedule_file("data/increment.cas.schedule");
  string expected(( istreambuf_iterator<char>(schedule_file) ),
                    istreambuf_iterator<char>());

  string args           = " simulate -v -s 0 ";
  string checker_file   = " data/increment.checker.asm ";
  string increment_file = " data/increment.cas.asm ";

  string cmd =
    executable + args + checker_file + increment_file + increment_file;

  string actual = shell.run(cmd);

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulate_missing_args ******************************************************/
TEST_F(MainTest, simulate_missing_args)
{
  string args = " simulate";

  string expected = "error: got nothing to run\n";

  string actual = shell.run(executable + args);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  actual = shell.run(executable + args + " -v");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: missing seed\n";

  actual = shell.run(executable + args + " -s");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: missing bound\n";

  actual = shell.run(executable + args + " -k");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());
}

/* simulate_file_not_found ****************************************************/
TEST_F(MainTest, simulate_file_not_found)
{
  string args = " simulate ";

  string program_file = "file_not_found";

  string cmd = executable + args + program_file;

  string actual = shell.run(cmd);

  string expected = "error: " + program_file + " not found\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulate_illegal_seed ******************************************************/
TEST_F(MainTest, simulate_illegal_seed)
{
  string args = " simulate -s WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd);

  string expected = "error: illegal seed [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulate_illegal_bound *****************************************************/
TEST_F(MainTest, simulate_illegal_bound)
{
  string args = " simulate -k WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd);

  string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replay_increment_0 *********************************************************/
TEST_F(MainTest, replay_increment_0)
{
  string schedule_file = "data/increment.invalid.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string expected(( istreambuf_iterator<char>(sfs) ),
                    istreambuf_iterator<char>());

  string args = " replay -v ";

  string cmd = executable + args + schedule_file;

  string actual = shell.run(cmd);

  ASSERT_EQ(1, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replay_increment_cas *******************************************************/
TEST_F(MainTest, replay_increment_cas)
{
  string schedule_file = "data/increment.cas.schedule";

  /* read expected schedule from file */
  ifstream sfs(schedule_file);
  string expected(( istreambuf_iterator<char>(sfs) ),
                    istreambuf_iterator<char>());

  string args = " replay -v ";

  string cmd = executable + args + schedule_file;

  string actual = shell.run(cmd);

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replay_missing_args ********************************************************/
TEST_F(MainTest, replay_missing_args)
{
  string args = " replay";

  string expected = "error: no schedule given\n";

  string actual = shell.run(executable + args);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  actual = shell.run(executable + args + " -v");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: missing bound\n";

  actual = shell.run(executable + args + " -k");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());
}

/* replay_file_not_found ******************************************************/
TEST_F(MainTest, replay_file_not_found)
{
  string args = " replay ";

  string program_file = "file_not_found";

  string cmd = executable + args + program_file;

  string actual = shell.run(cmd);

  string expected = "error: " + program_file + " not found\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replay_illegal_bound *******************************************************/
TEST_F(MainTest, replay_illegal_bound)
{
  string args = " replay -k WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd);

  string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* verify_pretend *************************************************************/
TEST_F(MainTest, verify_pretend)
{
  string args               = " verify -p 5 ";
  string program_file       = "data/load.store.arithmetic.asm";
  string specification_file = "data/load.store.arithmetic.spec.smt";

  string cmd = executable + args + program_file + " " + specification_file;

  /* read expected smt formula from file */
  ifstream ffs("data/load.store.arithmetic.encoded.smt");
  string expected(( istreambuf_iterator<char>(ffs) ),
                    istreambuf_iterator<char>());

  /* read specification from file */
  ifstream sfs(specification_file);
  string specification((istreambuf_iterator<char>(sfs)),
                        istreambuf_iterator<char>());

  expected += specification + "\n(check-sat)\n(exit)\n";

  string actual = shell.run(cmd);

  EXPECT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* verify_load_store_arithmetic ***********************************************/
TEST_F(MainTest, verify_load_store_arithmetic)
{
  string args               = " verify 5 ";
  string program_file       = "data/load.store.arithmetic.asm";
  string specification_file = "data/load.store.arithmetic.spec.smt";

  string cmd = executable + args + program_file + " " + specification_file;

  string expected = "unsat\n";

  string actual = shell.run(cmd);

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* verify_illegal_args ********************************************************/
TEST_F(MainTest, verify_illegal_args)
{
  executable      = executable + " verify ";
  string program  = "data/increment.cas.asm";

  /* no arguments */
  string expected = "error: too few arguments\n";

  string actual = shell.run(executable);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* unknown option */
  expected = "error: unknown option [-foo]\n";

  actual = shell.run(executable + "-foo 1 " + program);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* missing bound */
  expected = "error: illegal bound [" + program + "]\n";

  actual = shell.run(executable + program + " " + program);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* illegal bound (string) */
  expected = "error: illegal bound [WRONG]\n";

  actual = shell.run(executable + "WRONG " + program);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* illegal bound (0) */
  expected = "error: illegal bound [0]\n";

  actual = shell.run(executable + "0 " + program);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* constraint file (missing) */
  expected = "error: 1 not found\n";

  actual = shell.run(executable + "-c 1 " + program);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing constraints file\n";

  actual = shell.run(executable + "-p -v -c");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  /* constraint file (not found) */
  expected = "error: FILE not found\n";

  actual = shell.run(executable + "-c FILE 1 " + program);

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

/* verify_file_not_found ******************************************************/
TEST_F(MainTest, verify_file_not_found)
{
  string args = " verify 1 ";
  string cmd = executable + args;

  string expected = "error: file_not_found not found\n";

  string actual = shell.run(cmd + "file_not_found");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());

  actual = shell.run(cmd + "data/increment.asm file_not_found");

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}
