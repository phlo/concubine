#include <gtest/gtest.h>

#include <fstream>

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

const std::filesystem::path cwd = std::filesystem::current_path();

const std::string bin = cwd / "concubine";

const std::string sim_trace = "sim.trace";
const std::string smt_trace = "smt.trace";
const std::string sim_mmap = "sim.mmap";
const std::string smt_mmap = "smt.mmap";

struct Main : public ::testing::Test
{
  Shell shell;

  Main () { std::filesystem::current_path(cwd); }

  auto write_program_nop ()
    {
      std::filesystem::path path = fs::mktmp("1op.asm");
      fs::write(path, "HALT");
      return path;
    }

  auto write_program_infinite ()
    {
      std::filesystem::path path = fs::mktmp("infinite.asm");
      fs::write(path, "JZ 0");
      return path;
    }

  auto write_program_load (const std::string & address)
    {
      std::filesystem::path path = fs::mktmp("load." + address + ".asm");
      fs::write(path, "LOAD " + address);
      return path;
    }
};

// illegal command line ========================================================

TEST_F(Main, illegal_command_line)
{
  std::string actual = shell.run(bin + " WRONG").str();
  ASSERT_EQ(255, shell.last_exit_code());

  std::string expected = "error: no command given";
  actual = shell.run(bin + " help").str();
  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: unknown command FOO";
  actual = shell.run(bin + " help FOO").str();
  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

// simulate ====================================================================

TEST_F(Main, simulate)
{
  std::filesystem::current_path(fs::mktmp());

  std::string program = write_program_nop();

  ASSERT_EQ("", shell.run(bin + " simulate " + program + " " + program).str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(2, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, simulate_uninitialized)
{
  std::filesystem::current_path(fs::mktmp());

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " simulate " +
        write_program_load("0").string() + " " +
        write_program_load("1").string())
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(sim_trace);
  auto mmap = create_from_file<MMap>(sim_mmap);

  ASSERT_EQ(4, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
  ASSERT_EQ(mmap[1], trace.accu(1));
}

TEST_F(Main, simulate_missing_args)
{
  std::string expected = "error: got nothing to run\n";
  std::string actual = shell.run(bin + " simulate").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, simulate_program_file_not_found)
{
  std::string actual = shell.run(bin + " simulate FOO").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, simulate_bound)
{
  std::filesystem::current_path(fs::mktmp());

  std::string program = write_program_infinite();

  ASSERT_EQ("", shell.run(bin + " simulate -k 4 " + program).str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(5, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, simulate_bound_missing)
{
  std::string actual = shell.run(bin + " simulate -k").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: missing bound\n", actual);
}

TEST_F(Main, simulate_bound_illegal)
{
  std::string actual = shell.run(bin + " simulate -k FOO").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: illegal bound [FOO]\n", actual);
}

TEST_F(Main, simulate_mmap)
{
  std::filesystem::current_path(fs::mktmp());

  auto mmap_path = (cwd / "test/data/init.mmap").string();

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " simulate -m " + mmap_path + " " +
        write_program_load("1").string() + " " +
        write_program_load("2").string() + " " +
        write_program_load("3").string())
      .str());
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
  std::string actual = shell.run(bin + " simulate -m").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: missing path to memory map\n", actual);
}

TEST_F(Main, simulate_mmap_file_not_found)
{
  std::string actual = shell.run(bin + " simulate -m FOO").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, simulate_outfile)
{
  std::filesystem::current_path(fs::mktmp());

  std::string stem = "load";

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " simulate -o " + stem + " " +
        write_program_load("0").string())
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(stem + ".trace");
  auto mmap = create_from_file<MMap>(stem + ".mmap");

  ASSERT_EQ(2, trace.size());
  ASSERT_EQ(mmap[0], trace.accu(0));
}

TEST_F(Main, simulate_outfile_missing)
{
  std::string actual = shell.run(bin + " simulate -o").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: missing output file name\n", actual);
}

TEST_F(Main, simulate_seed)
{
  std::filesystem::current_path(fs::mktmp());

  std::string cmd =
    bin + " simulate -k 64 -s 0 " + write_program_infinite().string();

  ASSERT_EQ("", shell .run(cmd) .str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto t1 = create_from_file<Trace>(sim_trace);

  ASSERT_EQ("", shell.run(cmd).str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto t2 = create_from_file<Trace>(sim_trace);

  ASSERT_EQ(t1, t2);
}

TEST_F(Main, simulate_seed_missing)
{
  std::string actual = shell.run(bin + " simulate -s").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: missing seed\n", actual);
}

TEST_F(Main, simulate_seed_illegal)
{
  std::string actual = shell.run(bin + " simulate -s FOO").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: illegal seed [FOO]\n", actual);
}

TEST_F(Main, simulate_increment_check)
{
  auto outpath = fs::mktmp("simulate.increment.check.t2.k16");

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " simulate -s 0 -k 16 -o " + outpath.string() +
        " test/data/increment.check.thread.0.asm"
        " test/data/increment.check.thread.n.asm")
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  std::string expected = fs::read("test/data/increment.check.t2.k16.trace");
  std::string actual = fs::read(outpath += ".trace");
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, simulate_increment_cas)
{
  auto outpath = fs::mktmp("simulate.increment.cas.t2.k16");

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " simulate -s 0 -k 16 -o " + outpath.string() +
        " test/data/increment.cas.asm"
        " test/data/increment.cas.asm")
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  std::string expected = fs::read("test/data/increment.cas.t2.k16.trace");
  std::string actual = fs::read(outpath += ".trace");
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, simulate_indirect)
{
  auto outpath = fs::mktmp("simulate.indirect.t1");

  ASSERT_EQ(
    "",
    shell
      .run(
        bin +
        " simulate -s 0 -o " + outpath.string() +
        " test/data/indirect.asm")
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  std::string expected = fs::read("test/data/indirect.t1.trace");
  std::string actual = fs::read(outpath += ".trace");
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, simulate_halt)
{
  auto outpath = fs::mktmp("simulate.halt.t2");

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " simulate -s 0 -k 8 -o " + outpath.string() +
        " test/data/halt.asm"
        " test/data/halt.asm")
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  std::string expected = fs::read("test/data/halt.t2.trace");
  std::string actual = fs::read(outpath += ".trace");
  ASSERT_EQ(expected, actual);
}

// solve =======================================================================

TEST_F(Main, solve)
{
  std::filesystem::current_path(fs::mktmp());

  std::string program = write_program_nop();

  ASSERT_EQ(
    "",
    shell.run(
      bin + " solve -c /dev/null -e smtlib-functional -s boolector 10 " +
      program + " " + program)
    .str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(2, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, solve_uninitialized)
{
  std::filesystem::current_path(fs::mktmp());

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " solve -c /dev/null -e smtlib-functional -s boolector 4 " +
        write_program_load("0").string() + " " +
        write_program_load("1").string())
      .str());
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
  std::string actual = shell.run(bin + " solve").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_unknown_option)
{
  std::string expected = "error: unknown option [-FOO]\n";
  std::string actual = shell.run(bin + " solve -FOO 1").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_bound)
{
  std::filesystem::current_path(fs::mktmp());

  std::string program = write_program_infinite();

  ASSERT_EQ(
    "",
    shell
      .run(
        bin + " solve -c /dev/null -e smtlib-functional -s boolector 4 " +
        program)
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(5, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, solve_bound_illegal)
{
  std::string expected = "error: illegal bound [FOO]\n";
  std::string actual = shell.run(bin + " solve FOO BAR").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_bound_illegal_zero)
{
  std::string expected = "error: illegal bound [0]\n";
  std::string actual = shell.run(bin + " solve 0 FOO").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_program_file_not_found)
{
  std::string actual = shell.run(bin + " solve 1 FOO").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

TEST_F(Main, solve_constraints_missing)
{
  std::string expected = "error: missing constraints file\n";
  std::string actual = shell.run(bin + " solve -v -c").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_constraints_file_not_found)
{
  std::string actual =
    shell.run(bin + " solve -c FOO 1 test/data/halt.asm").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ("error: FOO not found\n", actual);
}

// TODO
TEST_F(Main, solve_encoder_smtlib_functional)
{
  std::filesystem::current_path(fs::mktmp());

  std::string program = write_program_nop();

  ASSERT_EQ(
    "",
    shell
      .run(bin + " solve -e smtlib-functional -s boolector 1 " + program)
      .str());
  ASSERT_EQ(0, shell.last_exit_code());

  auto trace = create_from_file<Trace>(smt_trace);

  ASSERT_EQ(2, trace.size());
  for (const auto & it : trace) ASSERT_EQ(0, it.pc);
  for (const auto & p : *trace.programs) ASSERT_EQ(program, p.path);
}

TEST_F(Main, solve_encoder_missing)
{
  std::string expected = "error: missing encoder\n";
  std::string actual = shell.run(bin + " solve -v -e").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_encoder_illegal)
{
  std::string expected = "error: unknown encoder [FOO]\n";
  std::string actual =
    shell.run(bin + " solve -e FOO 1 test/data/halt.asm").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, solve_pretend_cas)
{
  std::string cmd =
    bin +
    " solve -v -p 16 "
    " test/data/increment.cas.asm"
    " test/data/increment.cas.asm";

  std::string actual = shell.run(cmd).str();

  EXPECT_EQ(0, shell.last_exit_code());

  std::string expected = fs::read("test/data/increment.cas.t2.k16.btor2");
  ASSERT_EQ(expected + '\n', actual);
}

TEST_F(Main, solve_cas)
{
  std::string args = " solve -v 8 ";
  std::string program = "test/data/increment.cas.asm";
  std::string cmd = bin + args + program + " " + program;

  std::string expected = "sat";
  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  ASSERT_EQ("", actual);
}

TEST_F(Main, solve_illegal_args)
{
  std::string cmd = bin + " solve ";
  std::string program = "test/data/increment.cas.asm";

  // no arguments
  std::string expected = "error: too few arguments\n";
  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // unknown option
  expected = "error: unknown option [-foo]\n";
  actual = shell.run(cmd + "-foo 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // missing bound
  expected = "error: illegal bound [" + program + "]\n";
  actual = shell.run(cmd + program + " " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // illegal bound (std::string)
  expected = "error: illegal bound [WRONG]\n";
  actual = shell.run(cmd + "WRONG " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // illegal bound (0)
  expected = "error: illegal bound [0]\n";
  actual = shell.run(cmd + "0 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // constraint file missing
  expected = "error: 1 not found\n";
  actual = shell.run(cmd + "-c 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing constraints file\n";
  actual = shell.run(cmd + "-v -c").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // constraint file not found
  expected = "error: FILE not found\n";
  actual = shell.run(cmd + "-c FILE 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // encoder missing
  expected = "error: missing encoder\n";
  actual = shell.run(cmd + "-v -e").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // unknown encoder
  expected = "error: unknown encoder [FOO]\n";
  actual = shell.run(cmd + "-e FOO 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  // unknown solver
  expected = "error: unknown solver [FOO]\n";
  actual = shell.run(cmd + "-s FOO 1 " + program).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

// replay ======================================================================

TEST_F(Main, replay_increment_check)
{
  std::string path = "test/data/increment.check.t2.k16.trace";
  std::string cmd = bin + " replay " + path;

  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  std::string expected = fs::read(path);
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, replay_increment_cas)
{
  std::string path = "test/data/increment.cas.t2.k16.trace";
  std::string cmd = bin + " replay " + path;

  std::string actual = shell.run(cmd).str();

  ASSERT_EQ(0, shell.last_exit_code());
  std::string expected = fs::read(path);
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, replay_missing_args)
{
  std::string args = " replay";

  std::string expected = "error: no trace given\n";
  std::string actual = shell.run(bin + args).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  actual = shell.run(bin + args).str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));

  expected = "error: missing bound\n";

  actual = shell.run(bin + args + " -k").str();

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual.substr(0, expected.length()));
}

TEST_F(Main, replay_file_not_found)
{
  std::string args = " replay ";
  std::string program_file = "file_not_found";
  std::string cmd = bin + args + program_file;

  std::string actual = shell.run(cmd).str();
  std::string expected = "error: " + program_file + " not found\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

TEST_F(Main, replay_illegal_bound)
{
  std::string args = " replay -k WRONG ";
  std::string cmd = bin + args + "none.asm";

  std::string actual = shell.run(cmd).str();
  std::string expected = "error: illegal bound [WRONG]\n";

  ASSERT_EQ(255, shell.last_exit_code());
  ASSERT_EQ(expected, actual);
}

} // namespace ConcuBinE::test
