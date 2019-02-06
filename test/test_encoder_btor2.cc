#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct Btor2EncoderTest : public ::testing::Test
{
  const char *      expected;
  ProgramList       programs;
  Btor2EncoderPtr   encoder = create_encoder(1);

  Btor2EncoderPtr create_encoder (const word bound)
    {
      return make_shared<Btor2Encoder>(
        make_shared<ProgramList>(programs),
        bound,
        false);
    }

  void reset_encoder (const word bound)
    {
      encoder = create_encoder(bound);
    }

  void add_dummy_programs (unsigned num, unsigned size)
    {
      for (size_t i = 0; i < num; i++)
        {
          InstructionPtr op = Instruction::Set::create("ADDI", i + 1);
          programs.push_back(shared_ptr<Program>(new Program()));
          for (size_t j = 0; j < size; j++)
            programs[i]->add(op);
        }

      encoder = create_encoder(1);
    }
};

// void Btor2Encoder::declare_sorts ();
TEST_F(Btor2EncoderTest, declare_sorts)
{
  encoder->declare_sorts();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; sorts\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n\n",
    encoder->str());

  /* verbosity */
  reset_encoder(1);

  verbose = false;
  encoder->declare_sorts();
  verbose = true;

  ASSERT_EQ(
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n\n",
    encoder->str());
}

// void Btor2Encoder::declare_constants ();
TEST_F(Btor2EncoderTest, declare_constants)
{
  for (size_t t = 0; t < 3; t++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      for (size_t pc = 0; pc < 3; pc++)
        programs.back()->add(
          Instruction::Set::create("ADDI", t + pc + 1));
    }

  reset_encoder(1);

  encoder->declare_sorts();
  encoder->declare_constants();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; sorts\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n"
    "\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; constants\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "4 zero 1\n"
    "5 one 1\n"
    "6 zero 2\n"
    "7 one 2\n"
    "8 constd 2 2\n"
    "9 constd 2 3\n"
    "10 constd 2 4\n"
    "11 constd 2 5\n\n",
    encoder->str());

  /* verbosity */
  reset_encoder(1);

  verbose = false;
  encoder->declare_sorts();
  encoder->declare_constants();
  verbose = true;

  ASSERT_EQ(
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n"
    "\n"
    "4 zero 1\n"
    "5 one 1\n"
    "6 zero 2\n"
    "7 one 2\n"
    "8 constd 2 2\n"
    "9 constd 2 3\n"
    "10 constd 2 4\n"
    "11 constd 2 5\n\n",
    encoder->str());
}

// void add_bound ();
TEST_F(Btor2EncoderTest, add_bound)
{
  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->formula.str("");

  encoder->add_bound();

  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; bound\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "\n"
    "; step counter\n"
    "8 state 2 k\n"
    "9 init 2 8 6\n"
    "10 add 2 7 8\n"
    "11 next 2 8 10\n"
    "\n"
    "; bound (1)\n"
    "12 eq 1 7 8\n"
    "13 bad 12\n\n",
    encoder->formula.str());

  /* verbosity */
  reset_encoder(1);

  encoder->declare_sorts();
  encoder->declare_constants();
  encoder->formula.str("");

  verbose = false;
  encoder->add_bound();
  verbose = true;

  ASSERT_EQ(
    "8 state 2 k\n"
    "9 init 2 8 6\n"
    "10 add 2 7 8\n"
    "11 next 2 8 10\n"
    "\n"
    "12 eq 1 7 8\n"
    "13 bad 12\n\n",
    encoder->formula.str());
}

// void Btor2Encoder::preprocess ();
TEST_F(Btor2EncoderTest, preprocess)
{
  typedef map<word, string> ConstantMap;

  add_dummy_programs(3, 3);

  ASSERT_EQ(
    ConstantMap({{0, ""}, {1, ""}, {2, ""}, {3, ""}}),
    encoder->constants);
}
