#include <gtest/gtest.h>

#include "boolector.hh"
#include "encoder.hh"
#include "parser.hh"
#include "simulator.hh"

using namespace std;

struct BoolectorTest : public ::testing::Test
{
  string          constraints;
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

TEST_F(BoolectorTest, solve_check)
{
  /* concurrent increment using CHECK */
  string increment_0 = "data/increment.check.thread.0.asm";
  string increment_n = "data/increment.check.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = boolector.solve(*encoder, constraints);

  /*
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
  */

  ASSERT_EQ(
    "data/increment.check.thread.0.asm\n"
    "data/increment.check.thread.n.asm\n"
    ".\n"
    "# tid	pc	cmd	arg	accu	mem	heap\n"
    "0	0	STORE	0	0	0	{(0,0)}\n"
    "1	0	CHECK	0	0	0	{}\n"
    "0	2	LOAD	0	0	0	{}\n"
    "0	3	ADDI	1	1	0	{}\n"
    "0	4	STORE	0	1	0	{(0,1)}\n"
    "1	1	CHECK	1	0	0	{}\n"
    "1	2	LOAD	0	1	0	{}\n"
    "1	3	ADDI	1	2	0	{}\n"
    "1	4	STORE	0	2	0	{(0,2)}\n"
    "0	6	JNZ	1	1	0	{}\n"
    "1	5	JNZ	0	2	0	{}\n"
    "1	0	CHECK	0	2	0	{}\n"
    "0	2	LOAD	0	2	0	{}\n"
    "0	3	ADDI	1	3	0	{}\n"
    "0	4	STORE	0	3	0	{(0,3)}\n"
    "1	1	CHECK	1	2	0	{}\n",
    schedule->print());

  ofstream file {"/tmp/test.schedule"};
  file << schedule->print();
  file.close();

  SchedulePtr parsed {create_from_file<Schedule>("/tmp/test.schedule")};

  vector<vector<pair<unsigned long, word>>> pc_diff;
  for (size_t t = 0; t < schedule->pc_updates.size(); t++)
    {
      vector<pair<unsigned long, word>> diff;

      std::set_symmetric_difference(
        schedule->pc_updates[t].begin(), schedule->pc_updates[t].end(),
        parsed->pc_updates[t].begin(), parsed->pc_updates[t].end(),
        std::back_inserter(diff));

      pc_diff.push_back(diff);
    }

  cout << "pc diff" << eol;
  unsigned long thread = 0;
  for (const auto & updates : pc_diff)
    {
      for (const auto & [step, val] : updates)
        cout << "\t" << thread << ": {" << step << ", " << val << "}" << eol;
      thread++;
    }

  ASSERT_EQ(*parsed, *schedule);

  Simulator simulator {programs};

  SchedulePtr simulated {simulator.replay(*parsed)};

  ASSERT_EQ(*simulated, *schedule);
}

TEST_F(BoolectorTest, DISABLED_solve_cas)
{
  /* concurrent increment using CAS */
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
    "1	1	CHECK	0	0	0	{}\n"
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

TEST_F(BoolectorTest, encode_deadlock)
{
  /* deadlock after 3 steps -> unsat */
  programs->push_back(create_from_file<Program>("data/deadlock.thread.0.asm"));
  programs->push_back(create_from_file<Program>("data/deadlock.thread.1.asm"));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 3);

  string formula = encoder->str();

  ASSERT_FALSE(boolector.sat(formula));
}
