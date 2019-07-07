#include <gtest/gtest.h>

#include "encoder.hh"
#include "parser.hh"

namespace test::encoder {

template <class E, class Impl = E>
struct Encoder: public ::testing::Test
{
  using Type = Instruction::Type;

  Program::List programs;
  std::unique_ptr<E> encoder = create_encoder();

  virtual std::unique_ptr<E> init_encoder (std::unique_ptr<E> e)
    {
      return e;
    }

  std::unique_ptr<E> create_encoder (const bound_t bound = 1)
    {
      return
        init_encoder(
          std::make_unique<Impl>(
            std::make_shared<Program::List>(programs),
            bound,
            false));
    }

  Program create_program (const std::string code)
    {
      std::string path = "dummy.asm";
      std::istringstream inbuf {code};
      return Program(inbuf, path);
    }

  void reset_encoder (const bound_t bound = 1)
    {
      encoder = create_encoder(bound);
    }

  void add_dummy_programs (const word_t num_threads, const word_t length = 1)
    {
      std::ostringstream code;
      const char * op = "ADDI 1\n";

      for (size_t i = 0; i < length; i++)
        code << op;

      for (size_t i = 0; i < num_threads; i++)
        programs.push_back(create_program(code.str()));
    }

  void add_instruction_set (const word_t num_threads)
    {
      for (size_t i = 0; i < num_threads; i++)
        programs.push_back(
          create_program(
            "LOAD 1\n"  // 0
            "STORE 1\n" // 1
            "ADD 1\n"   // 2
            "ADDI 1\n"  // 3
            "SUB 1\n"   // 4
            "SUBI 1\n"  // 5
            "CMP 1\n"   // 6
            "JMP 8\n"   // 7
            "JZ 1\n"    // 8
            "JNZ 1\n"   // 9
            "JS 1\n"    // 10
            "JNS 1\n"   // 11
            "JNZNS 1\n" // 12
            "MEM 1\n"   // 13
            "CAS 1\n"   // 14
            "CHECK 1\n" // 15
            "EXIT 1\n"  // 16
          ));
    }

  void encode (const std::initializer_list<std::string> _programs,
               const std::string file,
               const bound_t bound,
               const char * dir = "data/")
    {
      for (const auto & p : _programs)
        programs.push_back(create_from_file<Program>(dir + p));

      encoder =
        std::make_unique<Impl>(
          std::make_shared<Program::List>(programs),
          bound);

      std::ifstream ifs(dir + file);

      std::string expected;
      expected.assign(std::istreambuf_iterator<char>(ifs),
                      std::istreambuf_iterator<char>());

      std::ofstream tmp("/tmp/" + file);
      tmp << encoder->str();

      ASSERT_EQ(expected, encoder->str());
    }
};

} // namespace test::encoder
