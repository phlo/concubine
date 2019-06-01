#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct EncoderTest : public ::testing::Test
{
  const char *  expected;
  Program_list  programs;
  Encoder_ptr   encoder = create_encoder(0);

  Program_ptr create_program (string code)
    {
      string path = "dummy.asm";
      istringstream inbuf {code};
      return make_shared<Program>(inbuf, path);
    }

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
      ostringstream code;
      const char * op = "ADDI 1\n";

      for (size_t i = 0; i < size; i++)
        code << op;

      for (size_t i = 0; i < num; i++)
        programs.push_back(create_program(code.str()));

      encoder = create_encoder(0);
    }
};

/* Encoder::Encoder ***********************************************************/
TEST_F(EncoderTest, constructor)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "CAS 1\n"   // 0
      "ADDI 1\n"  // 1
      "JNS 1\n"   // 2
      "CHECK 1\n" // 3
      "JNZ 6\n"   // 4
      "CHECK 2\n" // 5
      "EXIT 1\n"  // 6
    ));

  reset_encoder(0);

  for (const auto & pcs : encoder->flush_pcs)
    ASSERT_EQ(set<word_t>({0, 3, 5}), pcs.second);

  for (const auto & [id, threads] : encoder->check_pcs)
    for (const auto & pcs : threads)
      ASSERT_EQ(id == 1 ? set<word_t>({3}) : set<word_t>({5}), get<1>(pcs));

  for (const auto & [thread, pcs] : encoder->exit_pcs)
    {
      ASSERT_TRUE(!thread || thread < 3);
      ASSERT_EQ(vector<word_t>({6}), pcs);
    }

  ASSERT_EQ(Encoder::Set<word_t>({0, 1, 2}), encoder->cas_threads);
}

TEST_F(EncoderTest, constructor_flush_pcs)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "STORE 1\n"
      "FENCE\n"
      "CAS 1\n"
    ));

  reset_encoder(0);

  for (const auto & pcs : encoder->flush_pcs)
    ASSERT_EQ(set<word_t>({0, 1, 2}), pcs.second);
}

TEST_F(EncoderTest, constructor_check_pcs)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "CHECK 1\n"
      "CHECK 2\n"
      "CHECK 3\n"
    ));

  reset_encoder(0);

  for (const auto & [id, threads] : encoder->check_pcs)
    for (const auto & pcs : threads)
      {
        word_t thread = id - 1;
        ASSERT_EQ(set<word_t>({thread}), pcs.second);
      }
}

TEST_F(EncoderTest, constructor_exit_pcs)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program(
      "JNZ 2\n"
      "EXIT 1\n"
      "JNZ 4\n"
      "EXIT 2\n"
      "EXIT 3\n"
    ));

  reset_encoder(0);

  for (const auto & pcs : encoder->exit_pcs)
    ASSERT_EQ(vector<word_t>({1, 3, 4}), pcs.second);
}

TEST_F(EncoderTest, constructor_cas_threads)
{
  for (size_t i = 0; i < 3; i++)
    programs.push_back(create_program("CAS 1"));

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
