#include <gtest/gtest.h>

#include "encoder.hh"

using namespace std;

struct EncoderTest : public ::testing::Test
{
  const char *      expected;
  Program_list       programs;
  EncoderPtr        encoder = create_encoder(0);

  EncoderPtr create_encoder (const word_t bound)
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

// Encoder::Encoder (const Program_list_ptr, bound_t)
TEST_F(EncoderTest, constructor)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("CAS", 1));   // 0
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));  // 1
      programs[i]->push_back(Instruction::Set::create("JNS", 1));   // 2
      programs[i]->push_back(Instruction::Set::create("CHECK", 1));  // 3
      programs[i]->push_back(Instruction::Set::create("JMP", 6));   // 4
      programs[i]->push_back(Instruction::Set::create("EXIT", 1));  // 5
      programs[i]->push_back(Instruction::Set::create("CHECK", 2));  // 6
    }

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_THROW(predecessors.at(0), out_of_range);
      ASSERT_EQ(set<word_t>({0, 2}), predecessors.at(1));
      ASSERT_EQ(set<word_t>({1}), predecessors.at(2));
      ASSERT_EQ(set<word_t>({2}), predecessors.at(3));
      ASSERT_EQ(set<word_t>({3}), predecessors.at(4));
      ASSERT_THROW(predecessors.at(5), out_of_range);
      ASSERT_EQ(set<word_t>({4}), predecessors.at(6));
    }

  for (const auto & [id, threads] : encoder->check_pcs)
    for (const auto & pcs : threads)
      ASSERT_EQ(id == 1 ? set<word_t>({3}) : set<word_t>({6}), get<1>(pcs));

  for (const auto & pcs : encoder->exit_pcs)
      ASSERT_EQ(vector<word_t>({5}), get<1>(pcs));

  ASSERT_EQ(set<word_t>({0, 1, 2}), encoder->cas_threads);
}

TEST_F(EncoderTest, constructor_predecessors)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
    }

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_THROW(predecessors.at(0), out_of_range);
      ASSERT_EQ(set<word_t>({0}), predecessors.at(1));
      ASSERT_EQ(set<word_t>({1}), predecessors.at(2));
    }
}

TEST_F(EncoderTest, constructor_predecessors_jump)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("JNZ", 1));
    }

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_THROW(predecessors.at(0), out_of_range);
      ASSERT_EQ(set<word_t>({0, 2}), predecessors.at(1));
      ASSERT_EQ(set<word_t>({1}), predecessors.at(2));
    }

  /* jump to initial statement */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("JNZNS", 0));

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_EQ(set<word_t>({3}), predecessors.at(0));
      ASSERT_EQ(set<word_t>({0, 2}), predecessors.at(1));
      ASSERT_EQ(set<word_t>({1}), predecessors.at(2));
      ASSERT_EQ(set<word_t>({2}), predecessors.at(3));
    }
}

TEST_F(EncoderTest, constructor_predecessors_exit)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("EXIT", 1));
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
    }

  reset_encoder(0);

  ASSERT_TRUE(encoder->predecessors.empty());
}

TEST_F(EncoderTest, constructor_predecessors_extra)
{
  for (size_t i = 0; i < 3; i++)
    {
      programs.push_back(shared_ptr<Program>(new Program()));

      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
      programs[i]->push_back(Instruction::Set::create("ADDI", 1));
    }

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_THROW(predecessors.at(0), out_of_range);
      ASSERT_EQ(set<word_t>({0}), predecessors.at(1));
      ASSERT_EQ(set<word_t>({1}), predecessors.at(2));
    }

  /* jump */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("JMP", 1));

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_THROW(predecessors.at(0), out_of_range);
      ASSERT_EQ(set<word_t>({0, 3}), predecessors.at(1));
      ASSERT_EQ(set<word_t>({1}), predecessors.at(2));
      ASSERT_EQ(set<word_t>({2}), predecessors.at(3));
    }

  /* jump to initial statement */
  for (const auto & p : programs)
    p->push_back(Instruction::Set::create("JNZNS", 0));

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_EQ(set<word_t>({4}), predecessors.at(0));
      ASSERT_EQ(set<word_t>({0, 3}), predecessors.at(1));
      ASSERT_EQ(set<word_t>({1}), predecessors.at(2));
      ASSERT_EQ(set<word_t>({2}), predecessors.at(3));
      ASSERT_THROW(predecessors.at(4), out_of_range);
    }

  /* exit call */
  for (const auto & p : programs)
    p->insert(p->begin() + 1, Instruction::Set::create("EXIT", 1));

  reset_encoder(0);

  for (const auto & [thread, predecessors] : encoder->predecessors)
    {
      ASSERT_EQ(thread, encoder->thread++);
      ASSERT_EQ(set<word_t>({5}), predecessors.at(0));
      ASSERT_EQ(set<word_t>({0, 4}), predecessors.at(1));
      ASSERT_THROW(predecessors.at(2), out_of_range);
      ASSERT_EQ(set<word_t>({2}), predecessors.at(3));
      ASSERT_EQ(set<word_t>({3}), predecessors.at(4));
      ASSERT_THROW(predecessors.at(5), out_of_range);
    }
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
      ASSERT_EQ(set<word_t>({static_cast<word_t>(id - 1)}), get<1>(pcs));
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

  ASSERT_EQ(set<word_t>({0, 1, 2}), encoder->cas_threads);
}

// void iterate_threads (std::function<void(void)>)
TEST_F(EncoderTest, iterate_threads_void_void)
{
  add_dummy_programs(3, 3);

  word_t thread = 0;

  encoder->iterate_threads([&] { ASSERT_EQ(thread++, encoder->thread); });
}

// void iterate_threads (std::function<void(Program &)>)
TEST_F(EncoderTest, iterate_threads_void_program)
{
  add_dummy_programs(3, 3);

  word_t thread = 0;

  encoder->iterate_threads([&] (Program & p) {
    ASSERT_EQ(thread, encoder->thread);
    ASSERT_EQ(&*programs[thread++], &p);
  });
}

// void iterate_threads_reverse (std::function<void(Program &)>)
TEST_F(EncoderTest, iterate_threads_reverse_void_program)
{
  add_dummy_programs(3, 3);

  word_t thread = encoder->num_threads - 1;

  encoder->iterate_threads_reverse([&] (Program & p) {
    ASSERT_EQ(thread, encoder->thread);
    ASSERT_EQ(&*programs[thread--], &p);
  });
}

// string str (void)
TEST_F(EncoderTest, str)
{
  encoder->formula << "foo";

  ASSERT_EQ("foo", encoder->str());
}
