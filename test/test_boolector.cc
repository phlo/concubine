#include <gtest/gtest.h>

#include "boolector.hh"
#include "encoder.hh"
#include "parser.hh"

using namespace std;

struct BoolectorTest : public ::testing::Test
{
  Boolector       boolector;
  EncoderPtr      encoder;
  ProgramListPtr  programs = make_shared<ProgramList>();
  SchedulePtr     schedule;
};

TEST_F(BoolectorTest, sat)
{
  string formula = "(assert true)(check-sat)";

  ASSERT_TRUE(boolector.sat(formula));

  ASSERT_EQ("sat\n", boolector.std_out.str());
}

TEST_F(BoolectorTest, unsat)
{
  string formula = "(assert false)(check-sat)";

  ASSERT_FALSE(boolector.sat(formula));

  ASSERT_EQ("unsat\n", boolector.std_out.str());
}

TEST_F(BoolectorTest, solve_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = boolector.solve(*encoder, constraints);

  cout << "scheduled threads" << eol;
  for (const auto & [step, thread] : schedule->thread_updates)
    {
      cout << "\t{" << step << ", " << thread << "}" << eol;
    }

  cout << "pc updates" << eol;
  unsigned long thread = 0;
  for (const auto & updates : schedule->pc_updates)
    {
      for (const auto & [step, val] : updates)
        {
          cout << "\t" << thread << ": {" << step << ", " << val << "}" << eol;
        }
      thread++;
    }

  cout << "accu updates" << eol;
  thread = 0;
  for (const auto & updates : schedule->accu_updates)
    {
      for (const auto & [step, val] : updates)
        {
          cout << "\t" << thread << ": {" << step << ", " << val << "}" << eol;
        }
      thread++;
    }

  cout << "heap updates" << eol;
  for (const auto & updates : schedule->heap_updates)
    for (const auto & [idx, val] : updates.second)
      {
        cout << "\t{" << idx << ", " << val << "}" << eol;
      }

  ASSERT_EQ(
    "data/increment.sync.thread.0.asm\n"
    "data/increment.sync.thread.n.asm\n"
    ".\n"
    "# tid	pc	cmd	arg	accu	mem	heap\n"
    "0	0	STORE	0	0	0	{(0,0)}\n"
    "1	0	SYNC	0	0	0	{}\n"
    "0	2	LOAD	0	0	0	{}\n"
    "0	3	ADDI	1	1	0	{}\n"
    "0	4	STORE	0	1	0	{(0,1)}\n"
    "1	1	SYNC	1	0	0	{}\n"
    "1	2	LOAD	0	1	0	{}\n"
    "1	3	ADDI	1	2	0	{}\n"
    "1	4	STORE	0	2	0	{(0,2)}\n"
    "0	6	JNZ	1	1	0	{}\n"
    "1	5	JNZ	0	2	0	{}\n"
    "1	0	SYNC	0	2	0	{}\n"
    "0	2	LOAD	0	2	0	{}\n"
    "0	3	ADDI	1	3	0	{}\n"
    "0	4	STORE	0	3	0	{(0,3)}\n"
    "1	1	SYNC	1	2	0	{}\n",
    schedule->print());
}

TEST_F(BoolectorTest, DISABLED_solve_cas)
{
  /* concurrent increment using CAS */
  string constraints;
  string increment = "data/increment.cas.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = boolector.solve(*encoder, constraints);

  ASSERT_EQ(
    "data/increment.cas.asm\n"
    "data/increment.cas.asm\n"
    ".\n"
    "# tid	pc	cmd	arg	accu	mem	heap\n"
    "0	0	STORE	0	0	0	{(0,0)}\n"
    "1	0	STORE	0	0	0	{}\n"
    "1	1	SYNC	0	0	0	{}\n"
    "0	LOOP	MEM	0	0	0	{}\n"
    "1	LOOP	MEM	0	0	0	{}\n"
    "0	3	ADDI	1	1	0	{}\n"
    "0	4	CAS	0	1	0	{(0,1)}\n"
    "1	3	ADDI	1	1	0	{}\n"
    "1	4	CAS	0	0	0	{}\n"
    "0	5	JMP	LOOP	1	0	{}\n"
    "1	5	JMP	LOOP	0	0	{}\n"
    "0	LOOP	MEM	0	1	1	{}\n"
    "0	3	ADDI	1	2	1	{}\n"
    "0	4	CAS	0	1	1	{(0,2)}\n"
    "1	LOOP	MEM	0	2	2	{}\n"
    "1	3	ADDI	1	3	2	{}\n",
    schedule->print());
}
