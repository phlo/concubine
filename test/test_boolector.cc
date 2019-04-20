#include <gtest/gtest.h>

#include "boolector.hh"
#include "encoder.hh"
#include "parser.hh"
#include "streamredirecter.hh"

using namespace std;

struct BoolectorTest : public ::testing::Test
{
  Boolector       boolector;
  EncoderPtr      encoder;
  ProgramListPtr  programs = make_shared<ProgramList>();
  SchedulePtr     schedule;
};

TEST_F(BoolectorTest, sat)
{
  string formula = "(assert true)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", boolector.std_out.str());
}

TEST_F(BoolectorTest, unsat)
{
  string formula = "(assert false)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(boolector.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", boolector.std_out.str());
}

// TODO: remove
TEST_F(BoolectorTest, DISABLED_print_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 12);

  string formula = boolector.build_formula(*encoder, constraints);

  ASSERT_TRUE(boolector.sat(formula));

  cout << boolector.std_out.str();
}

TEST_F(BoolectorTest, DISABLED_solve_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = boolector.solve(*encoder, constraints);

  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->size());

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(increment_0, schedule->programs->at(0)->path);
  ASSERT_EQ(increment_n, schedule->programs->at(1)->path);

  ASSERT_EQ(
    vector<word>({0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1}),
    schedule->scheduled);

  cout << schedule->print();
}

TEST_F(BoolectorTest, DISABLED_solve_increment_multiple)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment = "data/increment.multiple.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = boolector.solve(*encoder, constraints);

  cout << schedule->print();
}

TEST_F(BoolectorTest, DISABLED_solve_missing_model)
{
  programs = make_shared<ProgramList>();

  programs->push_back(make_shared<Program>());

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 1);

  string constraints;

  boolector.solve(*encoder, constraints);
}

#include <boolector/boolector.h>
TEST_F(BoolectorTest, DISABLED_parse_smt2_c_api)
{
  const char * infile_name = "/tmp/boolector.smt2";

  Btor *btor = boolector_new();

  char *error_msg;
  int status;
  int result;
  FILE *infile = fopen (infile_name, "r");
  FILE *outfile = fopen ("/tmp/outfile", "w");
  result = boolector_parse (btor, infile, infile_name, outfile, &error_msg, &status);

  cout << "result = " << result << eol;
  cout << "status = " << status << eol;
  cout << "error msg = " << error_msg << eol;
}
