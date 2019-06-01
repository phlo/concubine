#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct EncoderTest : public ::testing::Test
{
  const char *  expected;
  Program_list  programs;
  Encoder_ptr   encoder = create_encoder(0);

  Encoder_ptr create_encoder (const word_t bound)
    {
      return make_shared<SMTLibEncoderFunctional>(
        make_shared<Program_list>(programs),
        bound,
        false);
    }

  void reset_encoder (const word_t bound)
    {
      encoder = create_encoder(bound);
      encoder->thread = 0;
    }

  void add_dummy_programs (unsigned num, unsigned size)
    {
      Instruction_ptr op = Instruction::Set::create("ADDI", 1);
      for (size_t i = 0; i < num; i++)
        {
          programs.push_back(shared_ptr<Program>(new Program()));
          for (size_t j = 0; j < size; j++)
            programs[i]->push_back(op);
        }

      encoder = create_encoder(0);
    }
};

/* Encoder::Encoder ***********************************************************/
TEST_F(EncoderTest, constructor)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("CAS", 1));   // 0
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));  // 1
      programs[i]->push_back(Instruction::Set::create("JNS", 1));   // 2
      programs[i]->push_back(Instruction::Set::create("CHECK", 1)); // 3
      programs[i]->push_back(Instruction::Set::create("JMP", 6));   // 4
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));  // 5
      programs[i]->push_back(Instruction::Set::create("CHECK", 2)); // 6
    }

  reset_encoder(0);

  for (const auto & [id, threads] : encoder->check_pcs)
    for (const auto & pcs : threads)
      ASSERT_EQ(
        id == 1 ? Encoder::Set<word_t>({3}) : Encoder::Set<word_t>({6}),
        get<1>(pcs));

  for (const auto & pcs : encoder->exit_pcs)
      ASSERT_EQ(vector<word_t>({5}), get<1>(pcs));

  ASSERT_EQ(Encoder::Set<word_t>({0, 1, 2}), encoder->cas_threads);
}

TEST_F(EncoderTest, constructor_check_pcs)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("CHECK", 1));
      programs[i]->push_back(Instruction::Set::create("CHECK", 2));
      programs[i]->push_back(Instruction::Set::create("CHECK", 3));
    }

  reset_encoder(0);

  for (const auto & [id, threads] : encoder->check_pcs)
    for (const auto & pcs : threads)
      ASSERT_EQ(
        Encoder::Set<word_t>({static_cast<word_t>(id - 1)}),
        get<1>(pcs));
}

TEST_F(EncoderTest, constructor_exit_pcs)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
      programs[i]->push_back(Instruction::Set::create("EXIT", 2));
      programs[i]->push_back(Instruction::Set::create("EXIT", 3));
    }

  reset_encoder(0);

  for (const auto & pcs : encoder->exit_pcs)
    ASSERT_EQ(vector<word_t>({0, 1, 2}), get<1>(pcs));
}

TEST_F(EncoderTest, constructor_cas_threads)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("CAS", 1));
    }

  reset_encoder(0);

  ASSERT_EQ(Encoder::Set<word_t>({0, 1, 2}), encoder->cas_threads);
}

/* Encoder::iterate_threads ***************************************************/
TEST_F(EncoderTest, iterate_threads)
{
  add_dummy_programs(3, 3);

  word_t thread = 0;

  encoder->iterate_threads([&] { ASSERT_EQ(thread++, encoder->thread); });
}

/* Encoder::iterate_programs **************************************************/
TEST_F(EncoderTest, iterate_programs)
{
  add_dummy_programs(3, 3);

  word_t thread = 0;

  encoder->iterate_programs([&] (const Program & p) {
    ASSERT_EQ(thread, encoder->thread);
    ASSERT_EQ(&*programs[thread++], &p);
  });
}

/* Encoder::iterate_programs_reverse ******************************************/
TEST_F(EncoderTest, iterate_programs_reverse)
{
  add_dummy_programs(3, 3);

  word_t thread = encoder->num_threads - 1;

  encoder->iterate_programs_reverse([&] (const Program & p) {
    ASSERT_EQ(thread, encoder->thread);
    ASSERT_EQ(&*programs[thread--], &p);
  });
}

/* Encoder::str ***************************************************************/
TEST_F(EncoderTest, str)
{
  encoder->formula << "foo";

  ASSERT_EQ("foo", encoder->str());
}
