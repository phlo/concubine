#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct Btor2EncoderTest : public ::testing::Test
{
  const char *      expected;
  ProgramList       programs;
  Btor2EncoderPtr   encoder = create_encoder(0);

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

      encoder = create_encoder(0);
    }
};

// void Btor2Encoder::declare_sorts ()
TEST_F(Btor2EncoderTest, declare_sorts)
{
  encoder->declare_sorts();

  ASSERT_EQ(
    "1 sort bitvec 1\n"
    "2 sort bitvec 16\n"
    "3 sort array 2 2\n",
    encoder->str());
}

// void Btor2Encoder::declare_constants ()
TEST_F(Btor2EncoderTest, declare_constants)
{
  // TODO
}

// void Btor2Encoder::preprocess ()
TEST_F(Btor2EncoderTest, preprocess)
{
  typedef map<word, string> ConstantMap;

  add_dummy_programs(3, 3);

  ASSERT_EQ(ConstantMap({{1, ""}, {2, ""}, {3, ""}}), encoder->constants);
}