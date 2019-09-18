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
  Shell shell;

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

  // run binary with given arguments
  //
  std::string run (std::initializer_list<std::string> args)
    {
      std::ostringstream oss(bin, std::ios_base::ate);
      for (const auto & arg : args)
        oss << " " << arg;
      return shell.run(oss.str()).str();
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
  run({"WRONG"});
  ASSERT_EQ(255, shell.last_exit_code());

  std::string expected = "error: no command given";
  std::string actual = run({"help"});
  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: unknown command FOO";
  actual = run({"help FOO"});
  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

// simulate ====================================================================

TEST_F(Main, simulate)
{
  fs::cd(tmpdir);

  std::string program = program_nop();

  ASSERT_EQ("", run({simulate, program, program}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(2, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, simulate_uninitialized)
{
  fs::cd(tmpdir);

  ASSERT_EQ("", run({simulate, program_load("0"), program_load("1")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(sim_trace);
  auto mmap = create_from_file<MMap>(sim_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, simulate_missing_args)
{
  std::string expected = "error: too few arguments\n";
  std::string actual = run({simulate});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, simulate_program_file_not_found)
{
  std::string actual = run({simulate, "FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, simulate_bound)
{
  fs::cd(tmpdir);

  ASSERT_EQ("", run({simulate, "-k 4", program_infinite()}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(5, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
}

TEST_F(Main, simulate_bound_missing)
{
  std::string expected = "error: missing bound\n";
  std::string actual = run({simulate, "-k"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, simulate_bound_illegal)
{
  std::string actual = run({simulate, "-k FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: illegal bound [FOO]\n", actual);
}

TEST_F(Main, simulate_mmap)
{
  fs::cd(tmpdir);

  ASSERT_EQ(
    "",
    run({
      simulate,
      "-m", cwd / "test/data/init.mmap",
      program_load("1"),
      program_load("2"),
      program_load("3")}));
  ASSERT_EQ(0, shell.last_exit_code());

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
  std::string expected = "error: missing path to memory map\n";
  std::string actual = run({simulate, "-m"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, simulate_mmap_file_not_found)
{
  std::string actual = run({simulate, "-m FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, simulate_outfile)
{
  fs::cd(tmpdir);

  std::string stem = "simulate.load";

  ASSERT_EQ("", run({simulate, "-o", stem, program_load("0")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(stem + ".trace");
  auto mmap = create_from_file<MMap>(stem + ".mmap");

  ASSERT_EQ(2, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
}

TEST_F(Main, simulate_outfile_missing)
{
  std::string expected = "error: missing output file name\n";
  std::string actual = run({simulate, "-o"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, simulate_seed)
{
  fs::cd(tmpdir);

  std::string program = program_infinite();
  std::string args = simulate + " -k 64 -s 0 " + program + " " + program;

  ASSERT_EQ("", run({args}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto t1 = create_from_file<Trace>(sim_trace);

  ASSERT_EQ("", run({args}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto t2 = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(t1, t2);
}

TEST_F(Main, simulate_seed_missing)
{
  std::string expected = "error: missing seed\n";
  std::string actual = run({simulate, "-s"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, simulate_seed_illegal)
{
  std::string actual = run({simulate, "-s FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: illegal seed [FOO]\n", actual);
}

// solve =======================================================================

TEST_F(Main, solve)
{
  fs::cd(tmpdir);

  std::string bound = "1";
  std::string program = program_nop();

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c", simulate_btor2(bound),
      bound,
      program,
      program}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(2, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, solve_uninitialized)
{
  fs::cd(tmpdir);

  std::string bound = "3";

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c", simulate_btor2(bound),
      bound,
      program_load("0"),
      program_load("1")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_missing_args)
{
  std::string expected = "error: too few arguments\n";
  std::string actual = run({solve});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_unknown_option)
{
  std::string expected = "error: unknown option [-FOO]\n";
  std::string actual = run({solve, "-FOO 1"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_bound)
{
  fs::cd(tmpdir);

  std::string bound = "4";

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c", simulate_btor2(bound),
      bound,
      program_infinite()}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(5, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
}

TEST_F(Main, solve_bound_illegal)
{
  std::string expected = "error: illegal bound [FOO]\n";
  std::string actual = run({solve, "FOO BAR"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_bound_illegal_zero)
{
  std::string expected = "error: illegal bound [0]\n";
  std::string actual = run({solve, "0 FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_program_file_not_found)
{
  std::string actual = run({solve, "1 FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, solve_constraints_missing)
{
  std::string expected = "error: missing constraints file\n";
  std::string actual = run({solve, "-v -c"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_constraints_file_not_found)
{
  std::string actual = run({solve, "-c FOO 1", program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, solve_encoder_btor2)
{
  std::string bound = "10";
  std::string expected = fs::read("test/data/halt.t2.k10.btor2");
  std::string actual =
    run({
      solve,
      "-c /dev/null",
      "-e btor2",
      "-p",
      "-v",
      bound,
      "test/data/halt.asm",
      "test/data/halt.asm"});

  ASSERT_EQ(expected.substr(0, actual.length()), actual);
}

TEST_F(Main, solve_encoder_smtlib_functional)
{
  ASSERT_EQ(
    fs::read("test/data/halt.t2.k10.functional.smt2"),
    run({
      solve,
      "-c /dev/null",
      "-e smtlib-functional",
      "-p",
      "-s boolector",
      "-v",
      "10",
      "test/data/halt.asm",
      "test/data/halt.asm"}));
}

TEST_F(Main, solve_encoder_smtlib_relational)
{
  ASSERT_EQ(
    fs::read("test/data/halt.t2.k10.relational.smt2"),
    run({
      solve,
      "-c /dev/null",
      "-e smtlib-relational",
      "-p",
      "-s boolector",
      "-v",
      "10",
      "test/data/halt.asm",
      "test/data/halt.asm"}));
}

TEST_F(Main, solve_encoder_missing)
{
  std::string expected = "error: missing encoder\n";
  std::string actual = run({solve, "-v -e"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_encoder_unknown)
{
  std::string expected = "error: unknown encoder [FOO]\n";
  std::string actual = run({solve, "-e FOO 1", program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_encoder_illegal_btor2_boolector)
{
  std::string actual =
    run({
      solve,
      "-e btor2",
      "-s boolector",
      "1",
      program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(
    "error: [boolector] cannot be used with encoder [btor2]\n",
    actual);
}

TEST_F(Main, solve_encoder_illegal_btor2_cvc4)
{
  std::string actual =
    run({
      solve,
      "-e btor2",
      "-s cvc4",
      "1",
      program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(
    "error: [cvc4] cannot be used with encoder [btor2]\n",
    actual);
}

TEST_F(Main, solve_encoder_illegal_btor2_z3)
{
  std::string actual =
    run({
      solve,
      "-e btor2",
      "-s z3",
      "1",
      program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(
    "error: [z3] cannot be used with encoder [btor2]\n",
    actual);
}

TEST_F(Main, solve_encoder_illegal_smtlib_functional_btormc)
{
  std::string actual =
    run({
      solve,
      "-e smtlib-functional",
      "-s btormc",
      "1",
      program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(
    "error: [btormc] cannot be used with encoder [smtlib-functional]\n",
    actual);
}

TEST_F(Main, solve_encoder_illegal_smtlib_relational_btormc)
{
  std::string actual =
    run({
      solve,
      "-e smtlib-relational",
      "-s btormc",
      "1",
      program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(
    "error: [btormc] cannot be used with encoder [smtlib-relational]\n",
    actual);
}

TEST_F(Main, solve_mmap)
{
  fs::cd(tmpdir);

  std::string bound = "6";

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c", simulate_btor2(bound),
      "-m", cwd / "test/data/init.mmap",
      bound,
      program_load("1"),
      program_load("2"),
      program_load("3")}));
  ASSERT_EQ(0, shell.last_exit_code());

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
  std::string expected = "error: missing path to memory map\n";
  std::string actual = run({solve, "-v -m"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_mmap_file_not_found)
{
  std::string actual = run({solve, "-m FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, solve_outfile)
{
  fs::cd(tmpdir);

  std::string bound = "2";
  std::string stem = "solve.load";

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c", simulate_btor2(bound),
      "-o", stem,
      bound,
      program_load("0")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(stem + ".trace");
  auto mmap = create_from_file<MMap>(stem + ".mmap");

  ASSERT_EQ(2, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
}

TEST_F(Main, solve_outfile_missing)
{
  std::string expected = "error: missing output file name\n";
  std::string actual = run({solve, "-v -o"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_pretend)
{
  std::string expected = "1 sort bitvec 1";
  std::string actual = run({solve, "-p", "1", program_nop()});

  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_solver_btormc)
{
  fs::cd(tmpdir);

  std::string bound = "3";

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c", simulate_btor2(bound),
      "-e btor2",
      "-s btormc",
      bound,
      program_load("0"),
      program_load("1")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_boolector)
{
  fs::cd(tmpdir);

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c /dev/null",
      "-e smtlib-functional",
      "-s boolector",
      "3",
      program_load("0"),
      program_load("1")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_cvc4)
{
  fs::cd(tmpdir);

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c /dev/null",
      "-e smtlib-functional",
      "-s cvc4",
      "3",
      program_load("0"),
      program_load("1")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_z3)
{
  fs::cd(tmpdir);

  ASSERT_EQ(
    "",
    run({
      solve,
      "-c /dev/null",
      "-e smtlib-functional",
      "-s z3",
      "3",
      program_load("0"),
      program_load("1")}));
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);
  auto mmap = create_from_file<MMap>(smt_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, solve_solver_missing)
{
  std::string expected = "error: missing solver\n";
  std::string actual = run({solve, "-v -s"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_solver_unknown)
{
  std::string expected = "error: unknown solver [FOO]\n";
  std::string actual = run({solve, "-s FOO 1", program_nop()});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_verbose)
{
  ASSERT_EQ(
    std::string::npos,
    run({solve, "-p 1", program_nop()}).find(';'));
  ASSERT_NE(
    std::string::npos,
    run({solve, "-p -v 1", program_nop()}).find(';'));
}

// replay ======================================================================

TEST_F(Main, replay)
{
  ASSERT_EQ("", run({replay, "test/data/halt.t2.trace"}));
  ASSERT_EQ(0, shell.last_exit_code());
}

TEST_F(Main, replay_trace_file_missing)
{
  std::string expected = "error: missing trace file\n";
  std::string actual = run({replay});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, replay_trace_file_not_found)
{
  std::string actual = run({simulate, "FOO"});

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

} // namespace ConcuBinE::test
