#include <gtest/gtest.h>

#include "btormc.hh"
#include "encoder.hh"
#include "parser.hh"
#include "simulator.hh"

namespace test {

//==============================================================================
// BtorMC tests
//==============================================================================

struct BtorMC : public ::testing::Test
{
  ::BtorMC btormc = ::BtorMC(16);
  Encoder::ptr encoder;
  Program::List::ptr programs = std::make_shared<Program::List>();
  Trace::ptr trace;
};

TEST_F(BtorMC, sat)
{
  std::string formula =
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

TEST_F(BtorMC, unsat)
{
  std::string formula =
    "1 sort bitvec 1\n"
    "2 state 1 x\n";

  ASSERT_FALSE(btormc.sat(formula));
  ASSERT_EQ("", btormc.std_out.str());
}

TEST_F(BtorMC, DISABLED_solve_check)
{
  // concurrent increment using CHECK
  std::string constraints;
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<btor2::Encoder>(programs, 16);

  trace = btormc.solve(*encoder, constraints);

  /*
  std::cout << "scheduled threads" << eol;
  for (const auto & [step, thread] : trace->thread_updates)
    {
      std::cout << "\t{" << step << ", " << thread << "}" << eol;
    }

  std::cout << "pc updates" << eol;
  unsigned long thread = 0;
  for (const auto & updates : trace->pc_updates)
    {
      for (const auto & [step, val] : updates)
        {
          std::cout << "\t" << thread << ": {" << step << ", " << val << "}" << eol;
        }
      thread++;
    }

  std::cout << "accu updates" << eol;
  thread = 0;
  for (const auto & updates : trace->accu_updates)
    {
      for (const auto & [step, val] : updates)
        {
          std::cout << "\t" << thread << ": {" << step << ", " << val << "}" << eol;
        }
      thread++;
    }

  std::cout << "heap updates" << eol;
  for (const auto & updates : trace->heap_updates)
    for (const auto & [idx, val] : updates.second)
      {
        std::cout << "\t{" << idx << ", " << val << "}" << eol;
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
    "0	6	JNZ	1	1	0	{}\n"
    "1	4	STORE	0	2	0	{(0,2)}\n"
    "1	5	JNZ	0	2	0	{}\n"
    "1	0	CHECK	0	2	0	{}\n"
    "0	2	LOAD	0	2	0	{}\n"
    "0	3	ADDI	1	3	0	{}\n"
    "0	4	STORE	0	3	0	{(0,3)}\n"
    "1	1	CHECK	1	2	0	{}\n"
    "1	2	LOAD	0	2	0	{}\n",
    trace->print());

  std::ofstream file {"/tmp/test.trace"};
  file << trace->print();
  file.close();

  Trace::ptr parsed =
    std::make_unique<Trace>(create_from_file<Trace>("/tmp/test.trace"));

  std::vector<std::vector<std::pair<bound_t, word_t>>> pc_diff;
  for (size_t t = 0; t < trace->pc_updates.size(); t++)
    {
      std::vector<std::pair<bound_t, word_t>> diff;

      std::set_symmetric_difference(
        trace->pc_updates[t].begin(), trace->pc_updates[t].end(),
        parsed->pc_updates[t].begin(), parsed->pc_updates[t].end(),
        std::back_inserter(diff));

      pc_diff.push_back(diff);
    }

  std::cout << "pc diff" << eol;
  word_t thread = 0;
  for (const auto & updates : pc_diff)
    {
      for (const auto & [step, val] : updates)
        std::cout
          << "\t" << thread << ": {" << step << ", " << val << "}"
          << eol;

      thread++;
    }

  ASSERT_EQ(*parsed, *trace);

  Simulator simulator {programs};

  Trace::ptr simulated {simulator.replay(*parsed)};

  ASSERT_EQ(*simulated, *trace);
}

TEST_F(BtorMC, DISABLED_solve_cas)
{
  // concurrent increment using CAS
  std::string constraints;
  std::string increment = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = std::make_unique<btor2::Encoder>(programs, 16);

  trace = btormc.solve(*encoder, constraints);

  ASSERT_EQ(
    "",
    // "data/increment.cas.asm\n"
    // "data/increment.cas.asm\n"
    // ".\n"
    // "# tid	pc	cmd	arg	accu	mem	heap\n"
    // "0	0	STORE	0	0	0	{(0,0)}\n"
    // "1	0	STORE	0	0	0	{}\n"
    // "1	1	CHECK	0	0	0	{}\n"
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
    trace->print());
}

// TODO: remove
TEST_F(BtorMC, print_model_check)
{
  // concurrent increment using CHECK
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<btor2::Encoder>(programs, 12);

  std::string formula = btormc.build_formula(*encoder, "");

  bool sat = btormc.sat(formula);

  std::ofstream outfile("/tmp/btormc.check.out");
  outfile << btormc.std_out.str();

  ASSERT_TRUE(sat);
}

TEST_F(BtorMC, print_model_cas)
{
  // concurrent increment using CAS
  std::string increment_cas = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_cas));
  programs->push_back(create_from_file<Program>(increment_cas));

  encoder = std::make_unique<btor2::Encoder>(programs, 12);

  std::string formula = btormc.build_formula(*encoder, "");

  bool sat = btormc.sat(formula);

  std::ofstream outfile("/tmp/btormc.cas.out");
  outfile << btormc.std_out.str();

  ASSERT_TRUE(sat);
}

} // namespace test
