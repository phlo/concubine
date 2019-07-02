#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"
#include "z3.hh"

namespace test {

//==============================================================================
// Z3 tests
//==============================================================================

struct Z3 : public ::testing::Test
{
  ::Z3 z3;
  Encoder::ptr encoder;
  Program::List::ptr programs = std::make_shared<Program::List>();
  Schedule::ptr schedule;
};

TEST_F(Z3, sat)
{
  std::string formula = "(assert true)(check-sat)";

  ASSERT_TRUE(z3.sat(formula));
}

TEST_F(Z3, unsat)
{
  std::string formula = "(assert false)(check-sat)";

  ASSERT_FALSE(z3.sat(formula));
}

TEST_F(Z3, solve_check)
{
  // concurrent increment using CHECK
  std::string constraints;
  std::string increment_0 = "data/increment.check.thread.0.asm";
  std::string increment_n = "data/increment.check.thread.n.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  schedule = z3.solve(*encoder, constraints);

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
    "0	5	CHECK	1	1	0	{}\n"
    "1	2	LOAD	0	1	0	{}\n"
    "1	3	ADDI	1	2	0	{}\n"
    "1	4	STORE	0	2	0	{(0,2)}\n"
    "1	5	JNZ	0	2	0	{}\n"
    "0	6	JNZ	1	1	0	{}\n"
    "1	0	CHECK	0	2	0	{}\n"
    "0	2	LOAD	0	2	0	{}\n"
    "0	3	ADDI	1	3	0	{}\n"
    "0	4	STORE	0	3	0	{(0,3)}\n"
    "0	5	CHECK	1	3	0	{}\n",
    schedule->print());
}

TEST_F(Z3, solve_cas)
{
  // concurrent increment using CAS
  std::string constraints;
  std::string increment = "data/increment.cas.asm";

  programs = std::make_shared<Program::List>();

  programs->push_back(create_from_file<Program>(increment));
  programs->push_back(create_from_file<Program>(increment));

  encoder = std::make_unique<smtlib::Functional>(programs, 16);

  schedule = z3.solve(*encoder, constraints);

  ASSERT_EQ(
    "data/increment.cas.asm\n"
    "data/increment.cas.asm\n"
    ".\n"
    "# tid	pc	cmd	arg	accu	mem	heap\n"
    "1	0	STORE	0	0	0	{(0,0)}\n"
    "0	0	STORE	0	0	0	{}\n"
    "1	1	CHECK	0	0	0	{}\n"
    "1	LOOP	MEM	0	0	0	{}\n"
    "1	3	ADDI	1	1	0	{}\n"
    "1	4	CAS	0	1	0	{(0,1)}\n"
    "1	5	JMP	LOOP	1	0	{}\n"
    "1	LOOP	MEM	0	1	1	{}\n"
    "1	3	ADDI	1	2	1	{}\n"
    "1	4	CAS	0	1	1	{(0,2)}\n"
    "1	5	JMP	LOOP	1	1	{}\n"
    "1	LOOP	MEM	0	2	2	{}\n"
    "1	3	ADDI	1	3	2	{}\n"
    "1	4	CAS	0	1	2	{(0,3)}\n"
    "1	5	JMP	LOOP	1	2	{}\n"
    "1	LOOP	MEM	0	3	3	{}\n",
    schedule->print());
}

} // namespace test
