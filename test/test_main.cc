#include <gtest/gtest.h>

#include <fstream>

#include "shell.hh"

using namespace std;

/* executable file name */
const char * executable = "../psimsmt";

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct MainTest : public ::testing::Test
{
  Shell shell;
};

/* illegalCommands ************************************************************/
TEST_F(MainTest, illegalCommands)
{
  string cmd = executable;

  string actual = shell.run(cmd + " WRONG");

  ASSERT_EQ(255, shell.lastExitCode());

  string expected = "error: no command given";

  actual = shell.run(cmd + " help");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: unknown command WRONG";

  actual = shell.run(cmd + " help WRONG");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());
}

/* simulateIncrement0 *********************************************************/
TEST_F(MainTest, simulateIncrement0)
{
  /* read expected schedule from file */
  ifstream scheduleFile("data/increment.invalid.schedule");
  string expected(( istreambuf_iterator<char>(scheduleFile) ),
                    istreambuf_iterator<char>());

  string args           = " simulate -v -s 0 ";
  string checkerFile    = " data/increment.checker.asm ";
  string incrementFile  = " data/increment.asm ";

  string cmd = executable + args + checkerFile + incrementFile + incrementFile;

  string actual = shell.run(cmd);

  ASSERT_EQ(1, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulateIncrementCAS *******************************************************/
TEST_F(MainTest, simulateIncrementCAS)
{
  /* read expected schedule from file */
  ifstream scheduleFile("data/increment.cas.schedule");
  string expected(( istreambuf_iterator<char>(scheduleFile) ),
                    istreambuf_iterator<char>());

  string args           = " simulate -v -s 0 ";
  string checkerFile    = " data/increment.checker.asm ";
  string incrementFile  = " data/increment.cas.asm ";

  string cmd = executable + args + checkerFile + incrementFile + incrementFile;

  string actual = shell.run(cmd);

  ASSERT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulateMissingArgs ********************************************************/
TEST_F(MainTest, simulateMissingArgs)
{
  string args = " simulate";

  string expected = "error: got nothing to run\n";

  string actual = shell.run(executable + args);

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  actual = shell.run(executable + args + " -v");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: missing seed\n";

  actual = shell.run(executable + args + " -s");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: missing bound\n";

  actual = shell.run(executable + args + " -k");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());
}

/* simulateFileNotFound *******************************************************/
TEST_F(MainTest, simulateFileNotFound)
{
  string args = " simulate ";

  string programFile = "file_not_found";

  string cmd = executable + args + programFile;

  string actual = shell.run(cmd);

  string expected = "error: " + programFile + " not found\n";

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulateIllegalSeed ********************************************************/
TEST_F(MainTest, simulateIllegalSeed)
{
  string args = " simulate -s WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd);

  string expected = "error: illegal seed [WRONG]\n";

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* simulateIllegalBound *******************************************************/
TEST_F(MainTest, simulateIllegalBound)
{
  string args = " simulate -k WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd);

  string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replayIncrement0 ***********************************************************/
TEST_F(MainTest, replayIncrement0)
{
  string scheduleFile = "data/increment.invalid.schedule";

  /* read expected schedule from file */
  ifstream sfs(scheduleFile);
  string expected(( istreambuf_iterator<char>(sfs) ),
                    istreambuf_iterator<char>());

  string args = " replay -v ";

  string cmd = executable + args + scheduleFile;

  string actual = shell.run(cmd);

  ASSERT_EQ(1, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replayIncrementCAS *********************************************************/
TEST_F(MainTest, replayIncrementCAS)
{
  string scheduleFile = "data/increment.cas.schedule";

  /* read expected schedule from file */
  ifstream sfs(scheduleFile);
  string expected(( istreambuf_iterator<char>(sfs) ),
                    istreambuf_iterator<char>());

  string args = " replay -v ";

  string cmd = executable + args + scheduleFile;

  string actual = shell.run(cmd);

  ASSERT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replayMissingArgs **********************************************************/
TEST_F(MainTest, replayMissingArgs)
{
  string args = " replay";

  string expected = "error: no schedule given\n";

  string actual = shell.run(executable + args);

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  actual = shell.run(executable + args + " -v");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: missing bound\n";

  actual = shell.run(executable + args + " -k");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());
}

/* replayFileNotFound *********************************************************/
TEST_F(MainTest, replayFileNotFound)
{
  string args = " replay ";

  string programFile = "file_not_found";

  string cmd = executable + args + programFile;

  string actual = shell.run(cmd);

  string expected = "error: " + programFile + " not found\n";

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* replayIllegalBound *********************************************************/
TEST_F(MainTest, replayIllegalBound)
{
  string args = " replay -k WRONG ";

  string cmd = executable + args + "none.asm";

  string actual = shell.run(cmd);

  string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* verifyPretend **************************************************************/
TEST_F(MainTest, verifyPretend)
{
  string args               = " verify -p 5 ";
  string programFile        = "data/load.store.arithmetic.asm";
  string specificationFile  = "data/load.store.arithmetic.spec.smt";

  string cmd = executable + args + programFile + " " + specificationFile;

  /* read expected smt formula from file */
  ifstream ffs("data/load.store.arithmetic.encoded.smt");
  string expected(( istreambuf_iterator<char>(ffs) ),
                    istreambuf_iterator<char>());

  /* read specification from file */
  ifstream sfs(specificationFile);
  string specification((istreambuf_iterator<char>(sfs)),
                        istreambuf_iterator<char>());

  expected += specification + "\n(check-sat)\n(exit)\n";

  string actual = shell.run(cmd);

  EXPECT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* verifyLoadStoreArithmetic **************************************************/
TEST_F(MainTest, verifyLoadStoreArithmetic)
{
  string args               = " verify 5 ";
  string programFile        = "data/load.store.arithmetic.asm";
  string specificationFile  = "data/load.store.arithmetic.spec.smt";

  string cmd = executable + args + programFile + " " + specificationFile;

  string expected = "unsat\n";

  string actual = shell.run(cmd);

  ASSERT_EQ(0, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}

/* verifyMissingArgs **********************************************************/
TEST_F(MainTest, verifyMissingArgs)
{
  string args = " verify";

  string expected = "error: too few arguments\n";

  string actual = shell.run(executable + args);

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: illegal bound [WRONG]\n";

  actual = shell.run(executable + args + " -p WRONG");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());

  expected = "error: illegal bound [0]\n";

  actual = shell.run(executable + args + " -p 0");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.substr(0, expected.length()).c_str());
}

/* verifyFileNotFound *********************************************************/
TEST_F(MainTest, verifyFileNotFound)
{
  string args = " verify 1 ";
  string cmd = executable + args;

  string expected = "error: file_not_found not found\n";

  string actual = shell.run(cmd + "file_not_found");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());

  actual = shell.run(cmd + "data/increment.asm file_not_found");

  ASSERT_EQ(255, shell.lastExitCode());
  ASSERT_STREQ(expected.c_str(), actual.c_str());
}
