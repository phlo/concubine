#include <gtest/gtest.h>

#include <fstream>

#include "btor2.hh"
#include "common.hh"
#include "fs.hh"
#include "mmap.hh"
#include "parser.hh"
#include "shell.hh"
#include "trace.hh"

namespace ConcuBinE::test {

//==============================================================================
// Main tests
//==============================================================================

// current working directory
const std::filesystem::path cwd = std::filesystem::current_path();

// temporary directory
const std::filesystem::path tmpdir = fs::mktmp("test/data/");

// binary path
const std::string bin = cwd / "concubine";

// module names
const std::string simulate = "simulate";
const std::string solve = "solve";
const std::string replay = "replay";

// default output file names
const std::string sim_trace = "sim.trace";
const std::string smt_trace = "smt.trace";
const std::string sim_mmap = "sim.mmap";
const std::string smt_mmap = "smt.mmap";

struct Main : public ::testing::Test
{
  Main () { fs::cd(cwd); }

  std::string program_nop ()
    {
      std::filesystem::path path = fs::mktmp("nop.asm");
      fs::write(path, "HALT");
      return path;
    }

  std::string program_infinite ()
    {
      std::filesystem::path path = fs::mktmp("infinite.asm");
      fs::write(path, "JZ 0");
      return path;
    }

  std::string program_load (const std::string & address)
    {
      std::filesystem::path path = fs::mktmp("load." + address + ".asm");
      fs::write(path, "LOAD " + address);
      return path;
    }

  // BTOR2 constraints for simulating a given number of steps
  //
  std::string simulate_btor2 (const std::string & bound = "")
    {
      std::filesystem::path path = fs::mktmp("bound." + bound + ".btor2");

      if (!std::filesystem::exists(path))
        {
          using namespace btor2;

          static const std::string sid_bool = "1";
          static const std::string sid_bv = "2";

          btor2::nid_t n = 1000000;
          std::string nid_0, nid_1, nid_b, nid_k, nid_prev;

          std::ofstream ofs(path);
          ofs << constd(nid_0 = std::to_string(n++), sid_bv, "0");
          ofs << constd(nid_1 = std::to_string(n++), sid_bv, "1");
          ofs << constd(nid_b = std::to_string(n++), sid_bv, bound);
          ofs << state(nid_k = std::to_string(n++), sid_bv, "k");
          ofs << init(std::to_string(n++), sid_bv, nid_k, nid_0);
          ofs << add(nid_prev = std::to_string(n++), sid_bv, nid_1, nid_k);
          ofs << next(std::to_string(n++), sid_bv, nid_k, nid_prev);
          ofs << eq(nid_prev = std::to_string(n++), sid_bool, nid_b, nid_k);
          ofs << bad(n);
        }

      return path;
    }
};

// illegal command line ========================================================

TEST_F(Main, illegal_command_line)
{
  auto out = shell::run({bin, "WRONG"});
  ASSERT_EQ(255, out.exit);

  out = shell::run({bin, "help"});
  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: no command given\n", out.stderr.str());

  out = shell::run({bin, "help", "FOO"});
  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: unknown command FOO\n", out.stderr.str());
}

// simulate ====================================================================

TEST_F(Main, simulate)
{
  fs::cd(tmpdir);

  const auto program = program_nop();
  const auto out = shell::run({bin, simulate, program, program});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(2, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, simulate_uninitialized)
{
  fs::cd(tmpdir);

  const auto out =
    shell::run({
      bin,
      simulate,
      program_load("0"),
      program_load("1")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(sim_trace);
  auto mmap = create_from_file<MMap>(sim_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, simulate_missing_args)
{
  const auto out = shell::run({bin, simulate});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: too few arguments\n", out.stderr.str());
}

TEST_F(Main, simulate_program_file_not_found)
{
  const auto out = shell::run({bin, simulate, "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: FOO not found\n", out.stderr.str());
}

TEST_F(Main, simulate_bound)
{
  fs::cd(tmpdir);

  const auto out = shell::run({bin, simulate, "-k", "4", program_infinite()});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(5, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
}

TEST_F(Main, simulate_bound_missing)
{
  const auto out = shell::run({bin, simulate, "-k"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing bound\n", out.stderr.str());
}

TEST_F(Main, simulate_bound_illegal)
{
  const auto out = shell::run({bin, simulate, "-k", "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: illegal bound [FOO]\n", out.stderr.str());
}

TEST_F(Main, simulate_mmap)
{
  fs::cd(tmpdir);

  const auto out =
    shell::run({
      bin,
      simulate,
      "-m", cwd / "test/data/init.mmap",
      program_load("1"),
      program_load("2"),
      program_load("3")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stderr.str());

  auto trace = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(sim_mmap, trace.mmap->path);

  auto mmap = create_from_file<MMap>(sim_mmap);

  ASSERT_EQ(6, trace.size());
  ASSERT_EQ(mmap[1], trace.accu(0));
  ASSERT_EQ(mmap[2], trace.accu(1));
  ASSERT_EQ(mmap[3], trace.accu(2));
}

TEST_F(Main, simulate_mmap_missing)
{
  const auto out = shell::run({bin, simulate, "-m"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing path to memory map\n", out.stderr.str());
}

TEST_F(Main, simulate_mmap_file_not_found)
{
  const auto out = shell::run({bin, simulate, "-m", "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: FOO not found\n", out.stderr.str());
}

TEST_F(Main, simulate_outfile)
{
  fs::cd(tmpdir);

  const std::string stem = "simulate.load";
  const auto out = shell::run({bin, simulate, "-o", stem, program_load("0")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(stem + ".trace");
  auto mmap = create_from_file<MMap>(stem + ".mmap");

  ASSERT_EQ(2, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
}

TEST_F(Main, simulate_outfile_missing)
{
  const auto out = shell::run({bin, simulate, "-o"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing output file name\n", out.stderr.str());
}

TEST_F(Main, simulate_seed)
{
  fs::cd(tmpdir);

  shell::Output out;
  const std::vector<std::string> cmd({
    bin,
    simulate,
    "-k", "64",
    "-s", "0",
    program_infinite(),
    program_infinite()
  });

  out = shell::run(cmd);
  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto t1 = create_from_file<Trace>(sim_trace);

  out = shell::run(cmd);
  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto t2 = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(t1, t2);
}

TEST_F(Main, simulate_seed_missing)
{
  const auto out = shell::run({bin, simulate, "-s"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing seed\n", out.stderr.str());
}

TEST_F(Main, simulate_seed_illegal)
{
  const auto out = shell::run({bin, simulate, "-s", "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: illegal seed [FOO]\n", out.stderr.str());
}

// solve =======================================================================

TEST_F(Main, solve)
{
  fs::cd(tmpdir);

  const std::string bound = "1";
  const auto program = program_nop();
  const auto out =
    shell::run({
      bin,
      solve,
      "-c", simulate_btor2(bound),
      bound,
      program,
      program});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(2, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, solve_uninitialized)
{
  fs::cd(tmpdir);

  const std::string bound = "3";
  const auto out =
    shell::run({
      bin,
      solve,
      "-c", simulate_btor2(bound),
      bound,
      program_load("0"),
      program_load("1")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_missing_args)
{
  const auto out = shell::run({bin, solve});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: too few arguments\n", out.stderr.str());
}

TEST_F(Main, solve_unknown_option)
{
  const auto out = shell::run({bin, solve, "-FOO", "1"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: unknown option [-FOO]\n", out.stderr.str());
}

TEST_F(Main, solve_bound)
{
  fs::cd(tmpdir);

  const std::string bound = "4";
  const auto out =
    shell::run({
      bin,
      solve,
      "-c", simulate_btor2(bound),
      bound,
      program_infinite()});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(5, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
}

TEST_F(Main, solve_bound_illegal)
{
  const auto out = shell::run({bin, solve, "FOO", "BAR"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: illegal bound [FOO]\n", out.stderr.str());
}

TEST_F(Main, solve_bound_illegal_zero)
{
  const auto out = shell::run({bin, solve, "0", "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: illegal bound [0]\n", out.stderr.str());
}

TEST_F(Main, solve_program_file_not_found)
{
  const auto out = shell::run({bin, solve, "1", "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: FOO not found\n", out.stderr.str());
}

TEST_F(Main, solve_constraints_missing)
{
  const auto out = shell::run({bin, solve, "-v", "-c"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing constraints file\n", out.stderr.str());
}

TEST_F(Main, solve_constraints_file_not_found)
{
  const auto out = shell::run({bin, solve, "-c", "FOO", "1", program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: FOO not found\n", out.stderr.str());
}

TEST_F(Main, solve_encoder_btor2)
{
  const auto expected = fs::read("test/data/halt.t2.k10.btor2");
  const auto actual =
    shell::run({
      bin,
      solve,
      "-c", "/dev/null",
      "-e", "btor2",
      "-p",
      "-v",
      "10",
      "test/data/halt.asm",
      "test/data/halt.asm"})
      .stdout.str();

  ASSERT_EQ(expected.substr(0, actual.length()), actual);
}

TEST_F(Main, solve_encoder_smtlib_functional)
{
  ASSERT_EQ(
    fs::read("test/data/halt.t2.k10.functional.smt2"),
    shell::run({
      bin,
      solve,
      "-c", "/dev/null",
      "-e", "smtlib-functional",
      "-p",
      "-s", "boolector",
      "-v",
      "10",
      "test/data/halt.asm",
      "test/data/halt.asm"})
      .stdout.str());
}

TEST_F(Main, solve_encoder_smtlib_relational)
{
  ASSERT_EQ(
    fs::read("test/data/halt.t2.k10.relational.smt2"),
    shell::run({
      bin,
      solve,
      "-c", "/dev/null",
      "-e", "smtlib-relational",
      "-p",
      "-s", "boolector",
      "-v",
      "10",
      "test/data/halt.asm",
      "test/data/halt.asm"})
      .stdout.str());
}

TEST_F(Main, solve_encoder_missing)
{
  const auto out = shell::run({bin, solve, "-v", "-e"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing encoder\n", out.stderr.str());
}

TEST_F(Main, solve_encoder_unknown)
{
  const auto out = shell::run({bin, solve, "-e", "FOO", "1", program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: unknown encoder [FOO]\n", out.stderr.str());
}

TEST_F(Main, solve_encoder_illegal_btor2_boolector)
{
  const auto out =
    shell::run({
      bin,
      solve,
      "-e", "btor2",
      "-s", "boolector",
      "1",
      program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ(
    "error: [boolector] cannot be used with encoder [btor2]\n",
    out.stderr.str());
}

TEST_F(Main, solve_encoder_illegal_btor2_cvc4)
{
  const auto out =
    shell::run({
      bin,
      solve,
      "-e", "btor2",
      "-s", "cvc4",
      "1",
      program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ(
    "error: [cvc4] cannot be used with encoder [btor2]\n",
    out.stderr.str());
}

TEST_F(Main, solve_encoder_illegal_btor2_z3)
{
  const auto out =
    shell::run({
      bin,
      solve,
      "-e", "btor2",
      "-s", "z3",
      "1",
      program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ(
    "error: [z3] cannot be used with encoder [btor2]\n",
    out.stderr.str());
}

TEST_F(Main, solve_encoder_illegal_smtlib_functional_btormc)
{
  const auto out =
    shell::run({
      bin,
      solve,
      "-e", "smtlib-functional",
      "-s", "btormc",
      "1",
      program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ(
    "error: [btormc] cannot be used with encoder [smtlib-functional]\n",
    out.stderr.str());
}

TEST_F(Main, solve_encoder_illegal_smtlib_relational_btormc)
{
  const auto out =
    shell::run({
      bin,
      solve,
      "-e", "smtlib-relational",
      "-s", "btormc",
      "1",
      program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ(
    "error: [btormc] cannot be used with encoder [smtlib-relational]\n",
    out.stderr.str());
}

TEST_F(Main, solve_mmap)
{
  fs::cd(tmpdir);

  const std::string bound = "6";
  const auto out =
    shell::run({
      bin,
      solve,
      "-c", simulate_btor2(bound),
      "-m", cwd / "test/data/init.mmap",
      bound,
      program_load("1"),
      program_load("2"),
      program_load("3")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(smt_mmap, trace.mmap->path);

  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(6, trace.size());
  ASSERT_EQ(mmap[1], trace.accu(0));
  ASSERT_EQ(mmap[2], trace.accu(1));
  ASSERT_EQ(mmap[3], trace.accu(2));
}

TEST_F(Main, solve_mmap_missing)
{
  const auto out = shell::run({bin, solve, "-v", "-m"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing path to memory map\n", out.stderr.str());
}

TEST_F(Main, solve_mmap_file_not_found)
{
  const auto out = shell::run({bin, solve, "-m", "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: FOO not found\n", out.stderr.str());
}

TEST_F(Main, solve_outfile)
{
  fs::cd(tmpdir);

  const std::string bound = "2";
  const std::string stem = "solve.load";
  const auto out =
    shell::run({
      bin,
      solve,
      "-c", simulate_btor2(bound),
      "-o", stem,
      bound,
      program_load("0")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(stem + ".trace");
  auto mmap = create_from_file<MMap>(stem + ".mmap");

  ASSERT_EQ(2, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
}

TEST_F(Main, solve_outfile_missing)
{
  const auto out = shell::run({bin, solve, "-v", "-o"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing output file name\n", out.stderr.str());
}

TEST_F(Main, solve_pretend)
{
  const std::string expected = "1 sort bitvec 1";
  const auto out = shell::run({bin, solve, "-p", "1", program_nop()});

  ASSERT_EQ(expected, out.stdout.str().substr(0, expected.length()));
}

TEST_F(Main, solve_solver_btormc)
{
  fs::cd(tmpdir);

  const std::string bound = "3";
  const auto out =
    shell::run({
      bin,
      solve,
      "-c", simulate_btor2(bound),
      "-e", "btor2",
      "-s", "btormc",
      bound,
      program_load("0"),
      program_load("1")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_boolector)
{
  fs::cd(tmpdir);

  const auto out =
    shell::run({
      bin,
      solve,
      "-c", "/dev/null",
      "-e", "smtlib-functional",
      "-s", "boolector",
      "3",
      program_load("0"),
      program_load("1")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_cvc4)
{
  fs::cd(tmpdir);

  const auto out =
    shell::run({
      bin,
      solve,
      "-c", "/dev/null",
      "-e", "smtlib-functional",
      "-s", "cvc4",
      "3",
      program_load("0"),
      program_load("1")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_z3)
{
  fs::cd(tmpdir);

  const auto out =
    shell::run({
      bin,
      solve,
      "-c", "/dev/null",
      "-e", "smtlib-functional",
      "-s", "z3",
      "3",
      program_load("0"),
      program_load("1")});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_missing)
{
  const auto out = shell::run({bin, solve, "-v", "-s"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing solver\n", out.stderr.str());
}

TEST_F(Main, solve_solver_unknown)
{
  const auto out = shell::run({bin, solve, "-s", "FOO", "1", program_nop()});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: unknown solver [FOO]\n", out.stderr.str());
}

TEST_F(Main, solve_verbose)
{
  const auto program = program_nop();

  ASSERT_EQ(
    std::string::npos,
    shell::run({bin, solve, "-p", "1", program}).stdout.str().find(';'));
  ASSERT_NE(
    std::string::npos,
    shell::run({bin, solve, "-p", "-v", "1", program}).stdout.str().find(';'));
}

// replay ======================================================================

TEST_F(Main, replay)
{
  const auto out = shell::run({bin, replay, "test/data/halt.t2.trace"});

  ASSERT_EQ(0, out.exit);
  ASSERT_EQ("", out.stdout.str());
}

TEST_F(Main, replay_trace_file_missing)
{
  const auto out = shell::run({bin, replay});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: missing trace file\n", out.stderr.str());
}

TEST_F(Main, replay_trace_file_not_found)
{
  const auto out = shell::run({bin, simulate, "FOO"});

  ASSERT_EQ(255, out.exit);
  ASSERT_EQ("error: FOO not found\n", out.stderr.str());
}

} // namespace ConcuBinE::test
