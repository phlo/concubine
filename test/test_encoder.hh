#include <gtest/gtest.h>

#include "encoder.hh"
#include "fs.hh"
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
template <class Encoder, bool simulation = false>
inline void encode (std::filesystem::path && basename,
                    const std::shared_ptr<Program::List> & programs,
                    const std::shared_ptr<MMap> & mmap,
                    const size_t bound)
{
  Encoder encoder(programs, mmap, bound);

  encoder.encode();

  if constexpr (simulation && std::is_base_of<btor2::Encoder, Encoder>::value)
    encoder.define_bound();

  if constexpr (simulation)
    basename += fs::ext<Encoder>(programs->size(), bound);
  else
    basename += fs::ext<Encoder>();

  std::ifstream ifs(basename);
  const std::string expected((std::istreambuf_iterator<char>(ifs)),
                              std::istreambuf_iterator<char>());
  const std::string actual = encoder.str();

  fs::write(fs::mktmp(basename), actual);
  ASSERT_EQ(expected, actual);
}

// =============================================================================
// simulation test encodings
// =============================================================================

// concurrent increment using checkpoints
//
template <class Encoder>
inline void encode_check ()
{
  const std::string basename = "test/data/increment.check";

  encode<Encoder, true>(
    basename,
    lst(
      create_from_file<Program>(basename + ".thread.0.asm"),
      create_from_file<Program>(basename + ".thread.n.asm")),
    nullptr,
    16);
}

// concurrent increment using compare and swap
//
template <class Encoder>
inline void encode_cas ()
{
  const std::string basename = "test/data/increment.cas";
  const auto program = create_from_file<Program>(basename + ".asm");

  encode<Encoder, true>(
    basename,
    lst(program, program),
    nullptr,
    16);
}

// indirect addressing
//
template <class Encoder>
inline void encode_indirect ()
{
  const std::string basename = "test/data/indirect.addressing";

  encode<Encoder, true>(
    basename,
    lst(create_from_file<Program>(basename + ".asm")),
    nullptr,
    9);
}

// halting mechanism
//
template <class Encoder>
inline void encode_halt ()
{
  const std::string basename = "test/data/halt";
  const auto program = create_from_file<Program>(basename + ".asm");

  encode<Encoder, true>(
    basename,
    lst(program, program),
    nullptr,
    10);
}

// =============================================================================
// litmus test encodings
// =============================================================================

// stores are not reordered with other stores
//
template <class Encoder>
inline void encode_litmus_intel_1 ()
{
  const std::filesystem::path dir("examples/litmus/intel/1");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    9);
}

// stores are not reordered with older loads
//
template <class Encoder>
inline void encode_litmus_intel_2 ()
{
  const std::filesystem::path dir("examples/litmus/intel/2");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    10);
}

// loads may be reordered with older stores
//
template <class Encoder>
inline void encode_litmus_intel_3 ()
{
  const std::filesystem::path dir("examples/litmus/intel/3");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    10);
}

// loads are not reordered with older stores to the same location
//
template <class Encoder>
inline void encode_litmus_intel_4 ()
{
  const std::filesystem::path dir("examples/litmus/intel/4");

  encode<Encoder>(
    dir / "formula",
    lst(create_from_file<Program>(dir / "processor.0.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    5);
}

// intra-processor forwarding is allowed
//
template <class Encoder>
inline void encode_litmus_intel_5 ()
{
  const std::filesystem::path dir("examples/litmus/intel/5");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    12);
}

// stores are transitively visible
//
template <class Encoder>
inline void encode_litmus_intel_6 ()
{
  const std::filesystem::path dir("examples/litmus/intel/6");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm"),
      create_from_file<Program>(dir / "processor.2.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    13);
}

// stores are seen in a consistent order by other processors
//
template <class Encoder>
inline void encode_litmus_intel_7 ()
{
  const std::filesystem::path dir("examples/litmus/intel/7");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm"),
      create_from_file<Program>(dir / "processor.2.asm"),
      create_from_file<Program>(dir / "processor.3.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    14);
}

// locked instructions have a total order
//
template <class Encoder>
inline void encode_litmus_intel_8 ()
{
  const std::filesystem::path dir("examples/litmus/intel/8");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm"),
      create_from_file<Program>(dir / "processor.2.asm"),
      create_from_file<Program>(dir / "processor.3.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    12);
}

// loads are not reordered with locks
//
template <class Encoder>
inline void encode_litmus_intel_9 ()
{
  const std::filesystem::path dir("examples/litmus/intel/9");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    8);
}

// stores are not reordered with locks
//
template <class Encoder>
inline void encode_litmus_intel_10 ()
{
  const std::filesystem::path dir("examples/litmus/intel/10");

  encode<Encoder>(
    dir / "formula",
    lst(
      create_from_file<Program>(dir / "processor.0.asm"),
      create_from_file<Program>(dir / "processor.1.asm")),
    mmap(create_from_file<MMap>(dir / "init.mmap")),
    8);
}

} // namespace ConcuBinE::test
