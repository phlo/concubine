#include <gtest/gtest.h>

#include "parser.hh"
#include "program.hh"
#include "streamredirecter.hh"

using namespace std;

/*******************************************************************************
 * Test Case Fixture
*******************************************************************************/
struct ProgramTest : public ::testing::Test
{
  Program program;
};

/* add ************************************************************************/
TEST_F(ProgramTest, add)
{
  program.add(Instruction::Set::create("ADD", 1));
  ASSERT_EQ(1, program.size());
  ASSERT_EQ(0, program.sync_ids.size());

  program.add(Instruction::Set::create("SYNC", 1));
  ASSERT_EQ(2, program.size());
  ASSERT_EQ(1, program.sync_ids.size());
  ASSERT_TRUE(program.sync_ids.find(1) != program.sync_ids.end());
}

/* parse **********************************************************************/
TEST_F(ProgramTest, parse)
{
  program = Program("data/increment.cas.asm");

  ASSERT_EQ(6, program.size());
  ASSERT_EQ(1, program.sync_ids.size());
  ASSERT_EQ(1, program.labels.size());
  ASSERT_EQ("LOOP", program.labels[2]);

  ASSERT_EQ("0\tSTORE\t0",  program.print(true, 0));
  ASSERT_EQ("1\tSYNC\t0",   program.print(true, 1));
  ASSERT_EQ("LOOP\tMEM\t0", program.print(true, 2));
  ASSERT_EQ("3\tADDI\t1",   program.print(true, 3));
  ASSERT_EQ("4\tCAS\t0",    program.print(true, 4));
  ASSERT_EQ("5\tJMP\tLOOP", program.print(true, 5));

  /* indirect addressing */
  program = Program("data/indirect.addressing.asm");

  ASSERT_EQ(5, program.size());
  ASSERT_EQ(0, program.sync_ids.size());
  ASSERT_EQ(0, program.labels.size());

  ASSERT_EQ("0\tADDI\t1",     program.print(true, 0));
  ASSERT_EQ("1\tSTORE\t[1]",  program.print(true, 1));
  ASSERT_EQ("2\tLOAD\t1",     program.print(true, 2));
  ASSERT_EQ("3\tADD\t[1]",    program.print(true, 3));
  ASSERT_EQ("4\tCMP\t[1]",    program.print(true, 4));
}

/* parse_file_not_found *******************************************************/
TEST_F(ProgramTest, parse_file_not_found)
{
  string file = "file_not_found";

  try
    {
      program = Program(file);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("file_not_found not found", e.what());
    }
}

/* parse_illegal_instruction **************************************************/
TEST_F(ProgramTest, parse_illegal_instruction)
{
  string dummy_file = "data/fibonacci.asm";

  Parser<Program> parser(dummy_file);

  /* illegal instruction */
  istringstream inbuf("NOP");

  StreamRedirecter redirecter(parser.file, inbuf);

  redirecter.start();

  try
    {
      parser.parse(&program);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("'NOP' unknown token", e.what());
    }

  redirecter.stop();

  /* illegal instruction argument (label) */
  inbuf.str("ADD nothing");

  redirecter.start();

  try
    {
      parser.parse(&program);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("ADD does not support labels", e.what());
    }

  redirecter.stop();

  /* illegal instruction argument (indirect addressing) */
  inbuf.str("SYNC [0]");

  redirecter.start();

  try
    {
      parser.parse(&program);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("SYNC does not support indirect addressing", e.what());
    }

  redirecter.stop();

  /* illegal instruction argument (label in indirect address) */
  inbuf.str("STORE [me]");

  redirecter.start();

  try
    {
      parser.parse(&program);
    }
  catch (const exception & e)
    {
      ASSERT_STREQ("indirect addressing does not support labels", e.what());
    }

  redirecter.stop();
}
