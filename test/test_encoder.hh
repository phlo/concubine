#include <gtest/gtest.h>

#include "encoder.hh"
#include "filesystem.hh"
#include "mmap.hh"
#include "parser.hh"

namespace ConcuBinE::test {

// =============================================================================
// variables
// =============================================================================

// program code containing the whole instruction set
//
const std::string instruction_set =
  "LOAD 1\n"  // 0
  "STORE 1\n" // 1
  "ADD 1\n"   // 2
  "ADDI 1\n"  // 3
  "SUB 1\n"   // 4
  "SUBI 1\n"  // 5
  "MUL 1\n"   // 6
  "MULI 1\n"  // 7
  "CMP 1\n"   // 8
  "JMP 10\n"  // 9
  "JZ 1\n"    // 10
  "JNZ 1\n"   // 11
  "JS 1\n"    // 12
  "JNS 1\n"   // 13
  "JNZNS 1\n" // 14
  "MEM 1\n"   // 15
  "CAS 1\n"   // 16
  "CHECK 1\n" // 17
  "EXIT 1\n"; // 18

// =============================================================================
// utility functions
// =============================================================================

// create program from source
//
inline Program prog (const std::string & code,
                     const std::string & path = "dummy.asm")
{
  std::istringstream inbuf (code);
  return Program(inbuf, path);
}

// create program list pointer from arbitrary number of programs
template <class ... P>
inline std::shared_ptr<Program::List> lst (P && ... programs)
{
  return std::make_shared<Program::List>(std::move(programs)...);
}

// create program list pointer containing duplicates of a given program
//
inline std::shared_ptr<Program::List> dup (Program && p, size_t times)
{
  auto programs = lst();

  while (times--)
    programs->push_back(p);

  return programs;
}

// create program list pointer containing dummy programs
//
inline std::shared_ptr<Program::List> dummy (const word_t threads,
                                             const word_t size = 1)
{
  std::ostringstream code;

  for (size_t i = 0; i < size; i++)
    code << "ADDI 1\n";

  auto programs = lst();

  for (size_t i = 0; i < threads; i++)
    programs->push_back(prog(code.str()));

  return programs;
}

// create memory map
//
inline std::shared_ptr<MMap> mmap (MMap && m = {})
{
  return std::make_shared<MMap>(m);
}

// initialize encoder
//
template <class Encoder>
inline Encoder init (Encoder e) { return e; }

// create encoder
//
template <class Encoder>
inline Encoder create (const Program::List::ptr & p = lst(),
                       const std::shared_ptr<MMap> & m = {},
                       const size_t b = 1)
{
  return init(Encoder(p, m, b));
}

// reset encoder
//
template <class Encoder>
inline void reset (Encoder & e, const std::optional<size_t> & bound = {})
{
  e = create<Encoder>(e.programs, e.mmap, bound.value_or(e.bound));
}

// encode programs and read expected formula from file
//
// NOTE: encoded formula stored in /tmp
//
template <class Encoder>
inline auto encode (const std::shared_ptr<Program::List> & programs,
                    const std::shared_ptr<MMap> & mmap,
                    const size_t bound,
                    const std::filesystem::path & formula)
{
  auto encoder = std::make_unique<Encoder>(programs, mmap, bound);

  encoder->encode();

  std::ifstream ifs(formula);
  auto expected =
    std::make_unique<std::string>(
      (std::istreambuf_iterator<char>(ifs)),
      std::istreambuf_iterator<char>());

  std::ofstream ofs(fs::mktmp(formula));
  ofs << encoder->str();

  return std::make_pair(std::move(encoder), std::move(expected));
}

// =============================================================================
// simulation test encodings
// =============================================================================

template <class Encoder>
inline void encode_simulation (const std::shared_ptr<Program::List> & programs,
                               const std::shared_ptr<MMap> & mmap,
                               const size_t bound,
                               const std::filesystem::path & formula)
{
  auto [encoder, expected] = encode<Encoder>(programs, mmap, bound, formula);

  if constexpr (std::is_base_of<btor2::Encoder, Encoder>::value)
    encoder->define_bound();

  ASSERT_EQ(*expected, encoder->str());
}

// concurrent increment using checkpoints
//
template <class Encoder>
inline void encode_check (const std::filesystem::path & formula)
{
  encode_simulation<Encoder>(
    lst(
      create_from_file<Program>("test/data/increment.check.thread.0.asm"),
      create_from_file<Program>("test/data/increment.check.thread.n.asm")),
    {},
    16,
    "test/data/" / formula);
}

// concurrent increment using compare and swap
//
template <class Encoder>
inline void encode_cas (const std::filesystem::path & formula)
{
  encode_simulation<Encoder>(
    lst(
      create_from_file<Program>("test/data/increment.cas.asm"),
      create_from_file<Program>("test/data/increment.cas.asm")),
    {},
    16,
    "test/data/" / formula);
}

// halting mechanism
//
template <class Encoder>
inline void encode_halt (const std::filesystem::path & formula)
{
  const auto name = "halt.asm";
  const auto code =
    "JNZ 2\n"
    "HALT\n"
    "EXIT 1\n";

  encode_simulation<Encoder>(
    lst(prog(code, name), prog(code, name)),
    {},
    10,
    "test/data/" / formula);
}

// =============================================================================
// litmus test encodings
// =============================================================================

template <class Encoder>
inline void encode_litmus (const std::shared_ptr<Program::List> & programs,
                           const std::shared_ptr<MMap> & mmap,
                           const size_t bound,
                           const std::filesystem::path & formula)
{
  auto [encoder, expected] = encode<Encoder>(programs, mmap, bound, formula);
  ASSERT_EQ(*expected, encoder->str());
}

// stores are not reordered with other stores
//
template <class Encoder>
inline void litmus_intel_1 (const std::filesystem::path & formula)
{
  const std::filesystem::path dir("examples/litmus/intel/1");

  encode_litmus<Encoder>(
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    9,
    dir / formula);
}

// stores are not reordered with older loads
//
template <class Encoder>
inline void litmus_intel_2 (const std::filesystem::path & formula)
{
  const std::filesystem::path dir("examples/litmus/intel/2");

  encode_litmus<Encoder>(
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    10,
    dir / formula);
}

// loads may be reordered with older stores
//
template <class Encoder>
inline void litmus_intel_3 (const std::filesystem::path & formula)
{
  const std::filesystem::path dir("examples/litmus/intel/3");

  encode_litmus<Encoder>(
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    10,
    dir / formula);
}

// loads are not reordered with older stores to the same location
//
template <class Encoder>
inline void litmus_intel_4 (const std::filesystem::path & formula)
{
  const std::filesystem::path dir("examples/litmus/intel/4");

  encode_litmus<Encoder>(
    lst(create_from_file<Program>(dir / "processor.0.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    5,
    dir / formula);
}

} // namespace ConcuBinE::test
