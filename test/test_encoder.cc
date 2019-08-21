#include "test_encoder.hh"

namespace ConcuBinE::test {

//==============================================================================
// Encoder tests
//==============================================================================

using E = smtlib::Functional;

// construction ================================================================

TEST(Encoder, constructor)
{
  const auto code =
    "CAS 1\n"   // 0
    "ADDI 1\n"  // 1
    "JNS 1\n"   // 2
    "CHECK 1\n" // 3
    "JNZ 6\n"   // 4
    "CHECK 2\n" // 5
    "EXIT 1\n"; // 6

  auto encoder = create<E>(dup(prog(code), 3));

  for (const auto & pcs : encoder.flush_pcs)
    ASSERT_EQ(std::vector<word_t>({0}), pcs.second);

  for (const auto & [id, threads] : encoder.check_pcs)
    for (const auto & pcs : threads)
      ASSERT_EQ(
        id == 1 ? std::vector<word_t>({3}) : std::vector<word_t>({5}),
        std::get<1>(pcs));

  ASSERT_TRUE(encoder.halt_pcs.empty());

  for (const auto & [thread, pcs] : encoder.exit_pcs)
    {
      ASSERT_TRUE(!thread || thread < 3);
      ASSERT_EQ(std::vector<word_t>({6}), pcs);
    }
}

TEST(Encoder, constructor_flush_pcs)
{
  const auto code =
    "STORE 1\n"
    "FENCE\n"
    "CAS 1\n"
    "HALT\n";

  auto encoder = create<E>(dup(prog(code), 3));

  for (const auto & p : *encoder.programs)
    ASSERT_EQ(4, p.size());

  for (const auto & pcs : encoder.flush_pcs)
    ASSERT_EQ(std::vector<word_t>({0, 1, 2, 3}), pcs.second);
}

TEST(Encoder, constructor_check_pcs)
{
  const auto code =
    "CHECK 1\n"
    "CHECK 2\n"
    "CHECK 3\n";

  auto encoder = create<E>(dup(prog(code), 3));

  for (const auto & [id, threads] : encoder.check_pcs)
    for (const auto & pcs : threads)
      {
        word_t thread = id - 1;
        ASSERT_EQ(std::vector<word_t>({thread}), pcs.second);
      }
}

TEST(Encoder, constructor_halt_pcs)
{
  auto programs = Program::list();

  for (size_t i = 0; i < 2; i++)
    if (i)
      programs->push_back(prog("ADDI 1\n"));
    else
      programs->push_back(prog(
        "JZ 2\n"
        "HALT\n"
        "ADDI 1\n"));

  auto encoder = create<E>(programs);

  ASSERT_EQ(std::vector<word_t>({1, 3}), encoder.halt_pcs[0]);
  ASSERT_EQ(std::vector<word_t>({1}), encoder.halt_pcs[1]);
}

TEST(Encoder, constructor_exit_pcs)
{
  const auto code =
    "JNZ 2\n"
    "EXIT 1\n"
    "JNZ 4\n"
    "EXIT 2\n"
    "EXIT 3\n";

  auto encoder = create<E>(dup(prog(code), 3));

  for (const auto & pcs : encoder.exit_pcs)
    ASSERT_EQ(std::vector<word_t>({1, 3, 4}), pcs.second);
}

// Encoder::iterate_threads ====================================================

TEST(Encoder, iterate_threads)
{
  auto encoder = create<E>(dummy(3, 3));

  word_t thread = 0;

  encoder.iterate_threads([&] { ASSERT_EQ(thread++, encoder.thread); });
}

// Encoder::iterate_programs ===================================================

TEST(Encoder, iterate_programs)
{
  auto programs = dummy(3, 3);
  auto encoder = create<E>(programs);

  word_t thread = 0;

  encoder.iterate_programs([&] (const Program & p) {
    ASSERT_EQ(thread, encoder.thread);
    ASSERT_EQ(&(*programs)[thread++], &p);
  });
}

// Encoder::iterate_programs_reverse ===========================================

TEST(Encoder, iterate_programs_reverse)
{
  auto programs = dummy(3, 3);
  auto encoder = create<E>(programs);

  word_t thread = encoder.num_threads - 1;

  encoder.iterate_programs_reverse([&] (const Program & p) {
    ASSERT_EQ(thread, encoder.thread);
    ASSERT_EQ(&(*programs)[thread--], &p);
  });
}

// Encoder::str ================================================================

TEST(Encoder, str)
{
  const auto str = "foo";
  auto encoder = create<E>();

  encoder.formula << str;
  ASSERT_EQ(str, encoder.str());
}

} // namespace ConcuBinE::test
