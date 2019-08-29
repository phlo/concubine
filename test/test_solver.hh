#include <gtest/gtest.h>

#include "btor2.hh"
#include "encoder.hh"
#include "filesystem.hh"
#include "mmap.hh"
#include "parser.hh"
#include "simulator.hh"
#include "smtlib.hh"
#include "trace.hh"

namespace ConcuBinE::test {

//==============================================================================
// Solver
//==============================================================================

template <class S, class E>
struct Solver : public ::testing::Test
{
  S solver;

  //----------------------------------------------------------------------------
  // simulation tests
  //----------------------------------------------------------------------------

  // generic simulation test function
  //
  void simulate (const Program::List::ptr & programs,
                 const std::shared_ptr<MMap> & mmap,
                 const size_t bound)
    {
      E encoder(programs, mmap, bound);

      encoder.encode();

      if constexpr(std::is_base_of<btor2::Encoder, E>::value)
        encoder.define_bound();

      auto trace = solver.solve(encoder);

      ASSERT_FALSE(trace->empty());

      // std::cout << "time to solve = " << solver.time << " ms" << eol;

      // std::cout << trace->print();

      auto replay = Simulator().replay(*trace);

      // std::cout << replay->print();

      ASSERT_EQ(*replay, *trace);
    }

  // concurrent increment using checkpoints
  //
  void solve_check ()
    {
      simulate(
        std::make_shared<Program::List>(
          create_from_file<Program>("test/data/increment.check.thread.0.asm"),
          create_from_file<Program>("test/data/increment.check.thread.n.asm")),
        nullptr,
        16);
    }

  // concurrent increment using compare and swap
  //
  void solve_cas ()
    {
      simulate(
        std::make_shared<Program::List>(
          create_from_file<Program>("test/data/increment.cas.asm"),
          create_from_file<Program>("test/data/increment.cas.asm")),
        nullptr,
        16);
    }

  // uninitialized indirect addressing
  //
  void solve_indirect ()
    {
      std::istringstream p0 (
        "LOAD [0]\n"
        "ADDI 1\n"
        "STORE [0]\n"
        "HALT\n");
      std::istringstream p1 (
        "LOAD [1]\n"
        "ADDI 1\n"
        "STORE [1]\n"
        "HALT\n");

      simulate(
        std::make_shared<Program::List>(
          Program(p0, "load.store.0.asm"),
          Program(p1, "load.store.1.asm")),
        nullptr,
        16);
    }

  //----------------------------------------------------------------------------
  // litmus tests
  //----------------------------------------------------------------------------

  // generic litmus test function
  //
  template <class SMTLib, class BTOR2, class Test>
  void encode_litmus (const std::filesystem::path & dir,
                      const std::shared_ptr<Program::List> & programs,
                      const std::shared_ptr<MMap> & mmap,
                      const size_t bound,
                      const SMTLib & constraints_smtlib [[maybe_unused]],
                      const BTOR2 & constraints_btor2 [[maybe_unused]],
                      const Test & test)
    {
      auto encoder = std::make_unique<E>(programs, mmap, bound);

      encoder->encode();

      std::ostringstream ss;
      std::string constraints;
      std::filesystem::path path;

      if constexpr(std::is_base_of<smtlib::Encoder, E>::value)
        {
          constraints_smtlib(ss);
          std::ofstream ofs(fs::mktmp(path = dir / "constraints.smt2"));
          constraints = ss.str();
          ofs << constraints;
        }
      else
        {
          constraints_btor2(ss, *encoder);
          std::ofstream ofs(fs::mktmp(path = dir / "constraints.btor2"));
          constraints = ss.str();
          ofs << constraints;
        }

      encoder->formula << constraints;

      test(*encoder);

      fs::update(path);
    }

  // stores are not reordered with other stores
  //
  void litmus_intel_1 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/1");

      constexpr size_t bound = 8;

      encode_litmus(
        dir,
        std::make_shared<Program::List>(
          create_from_file<Program>(dir / "processor.0.asm"),
          create_from_file<Program>(dir / "processor.1.asm")),
        std::make_shared<MMap>(create_from_file<MMap>(dir / "init.mmap")),
        bound,
        [] (std::ostringstream & ss) {
          std::vector<std::string> args;
          args.reserve(bound - 1);

          for (size_t k = 1; k < bound; k++)
            args.push_back(
              "\n    " +
              smtlib::land({
                smtlib::equality({
                  smtlib::Encoder::accu_var(k, 1),
                  smtlib::word2hex(1)}),
                smtlib::equality({
                  smtlib::Encoder::accu_var(k + 1, 1),
                  smtlib::word2hex(0)})}));

          ss <<
            smtlib::comment_section("litmus test constraints") <<
            smtlib::assertion("\n  " + smtlib::lor(args)) <<
            eol;
        },
        [] (std::ostringstream & ss, btor2::Encoder & e) {
          ss <<
            btor2::comment_section("litmus test constraints") <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[1],
              e.nids_accu[1]) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              "59") <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        [this] (E & e) {
          ASSERT_FALSE(solver.sat(solver.formula(e)));
        });
    }

  // stores are not reordered with older loads
  //
  void litmus_intel_2 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/2");

      constexpr size_t bound = 10;

      encode_litmus(
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
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[1],
              e.nids_mem[0]) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[1],
              e.nids_mem[1]) <<
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
        [this] (E & e) {
          ASSERT_FALSE(solver.sat(solver.formula(e)));
        });
    }

  // loads may be reordered with older stores
  //
  void litmus_intel_3 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/3");

      constexpr size_t bound = 10;

      encode_litmus(
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
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_mem[0]) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_mem[1]) <<
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
        [this, bound] (E & e) {
          auto trace = solver.solve(e);
          // std::cout << trace->print();
          ASSERT_EQ(bound, trace->size());
          ASSERT_EQ(*Simulator().replay(*trace), *trace);
        });
    }

  // loads are not reordered with older stores to the same location
  //
  void litmus_intel_4 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/4");

      constexpr size_t bound = 5;

      encode_litmus(
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
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_mem[0]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              e.nid_exit_flag,
              std::to_string(e.node - 1)) <<
            btor2::bad(e.node);
        },
        [this, bound] (E & e) {
          ASSERT_FALSE(solver.sat(solver.formula(e)));
        });
    }

  // intra-processor forwarding is allowed
  //
  void litmus_intel_5 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/5");

      constexpr size_t bound = 12;

      encode_litmus(
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
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_mem[0]) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_mem[1]) <<
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
        [this, bound] (E & e) {
          auto trace = solver.solve(e);
          // std::cout << trace->print();
          ASSERT_EQ(bound, trace->size());
          ASSERT_EQ(*Simulator().replay(*trace), *trace);
        });
    }

  // stores are transitively visible
  //
  void litmus_intel_6 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/6");

      constexpr size_t bound = 13;

      encode_litmus(
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
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[1],
              e.nids_mem[1]) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[1],
              e.nids_mem[2]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_accu[2]) <<
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
        [this, bound] (E & e) {
          ASSERT_FALSE(solver.sat(solver.formula(e)));
        });
    }

  // stores are seen in a consistent order by other processors
  //
  void litmus_intel_7 ()
    {
      const std::filesystem::path dir("examples/litmus/intel/7");

      constexpr size_t bound = 14;

      encode_litmus(
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
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[1],
              e.nids_mem[2]) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_accu[2]) <<
            btor2::land(
              e.nid(),
              e.sid_bool,
              std::to_string(e.node - 2),
              std::to_string(e.node - 1)) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[1],
              e.nids_mem[3]) <<
            btor2::eq(
              e.nid(),
              e.sid_bool,
              e.nids_const[0],
              e.nids_accu[3]) <<
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
        [this, bound] (E & e) {
          ASSERT_FALSE(solver.sat(solver.formula(e)));
        });
    }
};

} // namespace ConcuBinE::test
