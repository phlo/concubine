#include <gtest/gtest.h>

#include "btor2.hh"
#include "encoder.hh"
#include "fs.hh"
#include "mmap.hh"
#include "parser.hh"
#include "simulator.hh"
#include "smtlib.hh"
#include "trace.hh"

#include "solver.hh"

namespace ConcuBinE::test {

//==============================================================================
// Solver
//==============================================================================

template <class S>
struct Solver : public ::testing::Test
{
  S solver;

  //----------------------------------------------------------------------------
  // simulation tests
  //----------------------------------------------------------------------------

  // generic simulation test function
  //
  template <class Encoder>
  void simulate (const std::filesystem::path & stem,
                 const Program::List::ptr & programs,
                 const std::shared_ptr<MMap> & mmap,
                 const size_t bound)
    {
      using namespace fs;

      Encoder encoder(programs, mmap, bound);

      encoder.encode();

      if constexpr(std::is_base_of<btor2::Encoder, Encoder>::value)
        encoder.define_bound();

      const auto trace = solver.solve(encoder);

      ASSERT_FALSE(trace->empty());

      // std::cout << "time to solve = " << solver.time << " ms" << eol;

      const auto replay = Simulator().replay(*trace);
      const auto sext = '.' + solver.name();

      write(mktmp(stem, ext<Encoder>(programs->size(), bound)), encoder.str());
      write(mktmp(stem, ext<Encoder>(sext + ".trace")), trace->print());
      write(mktmp(stem, ext<Encoder>(sext + ".replay.trace")), replay->print());

      if constexpr(std::is_base_of<External, S>::value)
        write(mktmp(stem, ext<Encoder>(sext + ".model")), solver.std_out.str());

      ASSERT_EQ(*replay, *trace);
    }

  // concurrent increment using checkpoints
  //
  template <class Encoder>
  void simulate_check ()
    {
      const std::string basename = "test/data/increment.check";

      simulate<Encoder>(
        basename,
        std::make_shared<Program::List>(
          create_from_file<Program>(basename + ".thread.0.asm"),
          create_from_file<Program>(basename + ".thread.n.asm")),
        nullptr,
        16);
    }

  // concurrent increment using compare and swap
  //
  template <class Encoder>
  void simulate_cas ()
    {
      const std::string basename = "test/data/increment.cas";
      const auto program = create_from_file<Program>(basename + ".asm");

      simulate<Encoder>(
        basename,
        std::make_shared<Program::List>(program, program),
        nullptr,
        16);
    }

  // indirect addressing
  //
  template <class Encoder>
  void simulate_indirect ()
    {
      const std::string basename = "test/data/indirect.addressing";

      simulate<Encoder>(
        basename,
        std::make_shared<Program::List>(
          create_from_file<Program>(basename + ".asm")),
        nullptr,
        9);
    }

  // halting mechanism
  //
  template <class Encoder>
  void simulate_halt ()
    {
      const std::string basename = "test/data/halt";
      const auto program = create_from_file<Program>(basename + ".asm");

      simulate<Encoder>(
        basename,
        std::make_shared<Program::List>(program, program),
        nullptr,
        10);
    }

  //----------------------------------------------------------------------------
  // feature tests
  //----------------------------------------------------------------------------

  // verify indirect addressing
  //
  template <class Encoder>
  void verify_indirect ()
    {
      constexpr size_t bound = 9;

      Encoder encoder(
        std::make_shared<Program::List>(
          create_from_file<Program>("test/data/indirect.addressing.asm")),
        nullptr,
        bound);

      encoder.encode();

      if constexpr(std::is_base_of<smtlib::Encoder, Encoder>::value)
        encoder.formula <<
          smtlib::assertion(
            smtlib::lnot(
              smtlib::equality({
                smtlib::Encoder::accu_var(bound, 0),
                smtlib::word2hex(0)}))) <<
          eol;
      else
        encoder.formula <<
          btor2::ne(
            encoder.nid(),
            encoder.sid_bool,
            encoder.nids_const[0],
            encoder.nids_accu[0]) <<
          btor2::land(
            encoder.nid(),
            encoder.sid_bool,
            encoder.nid_exit_flag,
            std::to_string(encoder.node - 1)) <<
          btor2::bad(encoder.node);

      ASSERT_FALSE(solver.sat(solver.formula(encoder)));
    }

  //----------------------------------------------------------------------------
  // litmus tests
  //----------------------------------------------------------------------------

  // litmus test conditions for allowed examples
  //
  template <class Encoder>
  auto litmus_sat (const std::filesystem::path & dir)
    {
      return [this, &dir] (Encoder & e)
        {
          using namespace fs;

          const auto trace = solver.solve(e);

          ASSERT_FALSE(trace->empty());

          // std::cout << "time to solve = " << solver.time << " ms" << eol;

          const auto replay = Simulator().replay(*trace);
          const auto stem = dir / solver.name();

          write(mktmp(dir / "formula", ext<Encoder>()), e.str());
          write(mktmp(stem, ".trace"), trace->print());
          write(mktmp(stem, ".replay.trace"), replay->print());

          if constexpr(std::is_base_of<External, S>::value)
            write(mktmp(stem, ".model"), solver.std_out.str());

          ASSERT_EQ(e.bound, trace->size());
          ASSERT_EQ(*replay, *trace);
        };
    }

  // litmus test conditions for disallowed examples
  //
  template <class Encoder>
  auto litmus_unsat ()
    {
      return [this] (Encoder & encoder)
        {
          using namespace fs;

          ASSERT_FALSE(solver.sat(solver.formula(encoder)));
        };
    }

  // generic litmus test function
  //
  template <class Encoder, class SMTLib, class BTOR2, class Test>
  void litmus (const std::filesystem::path & dir,
               const std::shared_ptr<Program::List> & programs,
               const std::shared_ptr<MMap> & mmap,
               const size_t bound,
               const SMTLib & constraints_smtlib [[maybe_unused]],
               const BTOR2 & constraints_btor2 [[maybe_unused]],
               const Test & test)
    {
      using namespace fs;

      Encoder encoder(programs, mmap, bound);

      encoder.encode();

      std::ostringstream ss;
      std::string constraints;
      std::filesystem::path path;

      if constexpr(std::is_base_of<smtlib::Encoder, Encoder>::value)
        {
          constraints_smtlib(ss);
          std::ofstream ofs(mktmp(path = dir / "constraints.smt2"));
          constraints = ss.str();
          ofs << constraints;
        }
      else
        {
          constraints_btor2(ss, encoder);
          std::ofstream ofs(mktmp(path = dir / "constraints.btor2"));
          constraints = ss.str();
          ofs << constraints;
        }

      encoder.formula << constraints;
      write(mktmp(dir / "formula", ext<Encoder>()), encoder.str());
      test(encoder);
      update(path);
    }

  // Intel 1: stores are not reordered with other stores
  //
  template <class Encoder>
  void litmus_intel_1 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/1");

      constexpr size_t bound = 9;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 1),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // Intel 2: stores are not reordered with older loads
  //
  template <class Encoder>
  void litmus_intel_2 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/2");

      constexpr size_t bound = 10;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 0),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(1)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // Intel 3: loads may be reordered with older stores
  //
  template <class Encoder>
  void litmus_intel_3 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/3");

      constexpr size_t bound = 10;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 0),
                  smtlib::word2hex(0)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_sat<Encoder>(dir));
    }

  // Intel 4: loads are not reordered with older stores to the same location
  //
  template <class Encoder>
  void litmus_intel_4 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/4");

      constexpr size_t bound = 5;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::equality({
                smtlib::Encoder::mem_var(bound, 0),
                smtlib::word2hex(0)})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[0]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // Intel 5: intra-processor forwarding is allowed
  //
  template <class Encoder>
  void litmus_intel_5 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/5");

      constexpr size_t bound = 12;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 0),
                  smtlib::word2hex(0)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_sat<Encoder>(dir));
    }

  // Intel 6: stores are transitively visible
  //
  template <class Encoder>
  void litmus_intel_6 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/6");

      constexpr size_t bound = 13;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm"),
          create_from_file<Program>(dir / "processor.2.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 2),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 2),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[2]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[2]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // Intel 7: stores are seen in a consistent order by other processors
  //
  template <class Encoder>
  void litmus_intel_7 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/7");

      constexpr size_t bound = 14;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm"),
          create_from_file<Program>(dir / "processor.2.asm"),
          create_from_file<Program>(dir / "processor.3.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 2),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 2),
                  smtlib::word2hex(0)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 3),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 3),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[2]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[2]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[3]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[3]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 4),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // Intel 8: locked instructions have a total order
  //
  template <class Encoder>
  void litmus_intel_8 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/8");

      constexpr size_t bound = 12;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm"),
          create_from_file<Program>(dir / "processor.2.asm"),
          create_from_file<Program>(dir / "processor.3.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 2),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 2),
                  smtlib::word2hex(0)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 3),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 3),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[2]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[2]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[3]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[3]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 4),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // Intel 9: loads are not reordered with locks
  //
  template <class Encoder>
  void litmus_intel_9 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/9");

      constexpr size_t bound = 8;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 0),
                  smtlib::word2hex(0)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // Intel 10: stores are not reordered with locks
  //
  template <class Encoder>
  void litmus_intel_10 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/10");

      constexpr size_t bound = 8;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 1),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // AMD 1: loads and stores are not reordered
  //
  template <class Encoder>
  void litmus_amd_1 ()
    {
      const std::filesystem::path dir("examples/litmus/amd/1");

      constexpr size_t bound = 9;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(bound, 1),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_accu[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // AMD 2: stores do not pass loads
  //
  template <class Encoder>
  void litmus_amd_2 ()
    {
      const std::filesystem::path dir("examples/litmus/amd/2");

      constexpr size_t bound = 10;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 0),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(1)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }

  // AMD 3: stores can be arbitrarily delayed
  //
  template <class Encoder>
  void litmus_amd_3 ()
    {
      const std::filesystem::path dir("examples/litmus/amd/3");

      constexpr size_t bound = 16;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        nullptr,
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 0),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(1)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_sat<Encoder>(dir));
    }

  // AMD 4: non-overlapping loads may pass stores
  //
  template <class Encoder>
  void litmus_amd_4 ()
    {
      const std::filesystem::path dir("examples/litmus/amd/4");

      constexpr size_t bound = 10;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          const auto zero = smtlib::word2hex(0);
          const auto one = smtlib::word2hex(1);
          const auto mem_0 = smtlib::Encoder::mem_var(bound, 0);
          const auto mem_1 = smtlib::Encoder::mem_var(bound, 1);
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::lor({
                  smtlib::equality({mem_0, zero}),
                  smtlib::equality({mem_0, one})
                }),
                smtlib::lor({
                  smtlib::equality({mem_1, zero}),
                  smtlib::equality({mem_1, one})})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          std::string or_0, or_1;
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[0]) <<
            btor2::lor(
              or_0 = e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[1]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[1], e.nids_mem[1]) <<
            btor2::lor(
              or_1 = e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(e.nid(), e.sid_bool, or_0, or_1) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_sat<Encoder>(dir));
    }

  // AMD 5: sequential consistency
  //
  template <class Encoder>
  void litmus_amd_5 ()
    {
      const std::filesystem::path dir("examples/litmus/amd/5");

      constexpr size_t bound = 12;

      litmus<Encoder>(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion(
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 0),
                  smtlib::word2hex(0)}),
                smtlib::equality({
                  smtlib::Encoder::mem_var(bound, 1),
                  smtlib::word2hex(0)})})) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[0]) <<
            btor2::eq(e.nid(), e.sid_bool, e.nids_const[0], e.nids_mem[1]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        litmus_unsat<Encoder>());
    }
};

} // namespace ConcuBinE::test
