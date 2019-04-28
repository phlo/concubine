#include <gtest/gtest.h>

#include "btormc.hh"
#include "encoder.hh"
#include "parser.hh"

using namespace std;

struct BtorMCTest : public ::testing::Test
{
  BtorMC btormc = BtorMC(16);
  EncoderPtr      encoder;
  ProgramListPtr  programs = make_shared<ProgramList>();
  SchedulePtr     schedule;
};

TEST_F(BtorMCTest, sat)
{
  string formula =
    "1 sort bitvec 1\n"
    "2 state 1 x\n"
    "3 bad 2\n";

  ASSERT_TRUE(btormc.sat(formula));
  ASSERT_EQ(
    "sat\n"
    "b0 \n"
    "#0\n"
    "0 1 x#0\n"
    "@0\n"
    ".\n",
    btormc.std_out.str());
}

TEST_F(BtorMCTest, unsat)
{
  string formula =
    "1 sort bitvec 1\n"
    "2 state 1 x\n";

  ASSERT_FALSE(btormc.sat(formula));
  ASSERT_EQ("", btormc.std_out.str());
}

TEST_F(BtorMCTest, solve_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<Btor2Encoder>(programs, 16);

  schedule = btormc.solve(*encoder, constraints);

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

  cout << schedule->print();

  ASSERT_EQ(
    "",
    // "data/increment.sync.thread.0.asm\n"
    // "data/increment.sync.thread.n.asm\n"
    // ".\n"
    // "# tid	pc	cmd	arg	accu	mem	heap\n"
    // "0	0	STORE	0	0	0	{(0,0)}\n"
    // "1	0	SYNC	0	0	0	{}\n"
    // "0	2	LOAD	0	0	0	{}\n"
    // "0	3	ADDI	1	1	0	{}\n"
    // "0	4	STORE	0	1	0	{(0,1)}\n"
    // "1	1	SYNC	1	0	0	{}\n"
    // "1	2	LOAD	0	1	0	{}\n"
    // "1	3	ADDI	1	2	0	{}\n"
    // "1	4	STORE	0	2	0	{(0,2)}\n"
    // "0	6	JNZ	1	1	0	{}\n"
    // "1	5	JNZ	0	2	0	{}\n"
    // "1	0	SYNC	0	2	0	{}\n"
    // "0	2	LOAD	0	2	0	{}\n"
    // "0	3	ADDI	1	3	0	{}\n"
    // "0	4	STORE	0	3	0	{(0,3)}\n"
    // "1	1	SYNC	1	2	0	{}\n",
    schedule->print());
}

TEST_F(BtorMCTest, DISABLED_solve_cas)
{
  /* concurrent increment using CAS */
  string constraints;
  string increment = "data/increment.cas.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = make_shared<Btor2Encoder>(programs, 16);

  schedule = btormc.solve(*encoder, constraints);

  ASSERT_EQ(
    "",
    // "data/increment.cas.asm\n"
    // "data/increment.cas.asm\n"
    // ".\n"
    // "# tid	pc	cmd	arg	accu	mem	heap\n"
    // "0	0	STORE	0	0	0	{(0,0)}\n"
    // "1	0	STORE	0	0	0	{}\n"
    // "1	1	SYNC	0	0	0	{}\n"
    // "0	LOOP	MEM	0	0	0	{}\n"
    // "1	LOOP	MEM	0	0	0	{}\n"
    // "0	3	ADDI	1	1	0	{}\n"
    // "0	4	CAS	0	1	0	{(0,1)}\n"
    // "1	3	ADDI	1	1	0	{}\n"
    // "1	4	CAS	0	0	0	{}\n"
    // "0	5	JMP	LOOP	1	0	{}\n"
    // "1	5	JMP	LOOP	0	0	{}\n"
    // "0	LOOP	MEM	0	1	1	{}\n"
    // "0	3	ADDI	1	2	1	{}\n"
    // "0	4	CAS	0	1	1	{(0,2)}\n"
    // "1	LOOP	MEM	0	2	2	{}\n"
    // "1	3	ADDI	1	3	2	{}\n",
    schedule->print());
}
