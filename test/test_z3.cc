#include <gtest/gtest.h>

#include <sstream>

#include "encoder.hh"
#include "parser.hh"
#include "streamredirecter.hh"
#include "z3.hh"

using namespace std;

struct Z3Test : public ::testing::Test
{
  Z3              z3;
  EncoderPtr      encoder;
  ProgramListPtr  programs = make_shared<ProgramList>();
  SchedulePtr     schedule;
};

TEST_F(Z3Test, sat)
{
  string formula = "(assert true)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_TRUE(z3.sat(formula));

  redirecter.stop();

  ASSERT_EQ("sat\n", z3.std_out.str());
}

TEST_F(Z3Test, unsat)
{
  string formula = "(assert false)(check-sat)";

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  redirecter.start();

  ASSERT_FALSE(z3.sat(formula));

  redirecter.stop();

  ASSERT_EQ("unsat\n", z3.std_out.str());
}

// TODO: remove
TEST_F(Z3Test, DISABLED_print_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 12);

  string formula = z3.build_formula(*encoder, constraints);

  bool sat = z3.sat(formula);
  cout << z3.std_out.str();

  // ASSERT_TRUE(z3.sat(formula));
  ASSERT_TRUE(sat);
}

TEST_F(Z3Test, solve_sync)
{
  /* concurrent increment using SYNC */
  string constraints;
  string increment_0 = "data/increment.sync.thread.0.asm";
  string increment_n = "data/increment.sync.thread.n.asm";

  programs = make_shared<ProgramList>();

  programs->push_back(create_from_file<Program>(increment_0));
  programs->push_back(create_from_file<Program>(increment_n));

  encoder = make_shared<SMTLibEncoderFunctional>(programs, 16);

  schedule = z3.solve(*encoder, constraints);

  /*
  ASSERT_EQ(0, schedule->exit);
  ASSERT_EQ(16, schedule->size());

  ASSERT_EQ(2, schedule->programs->size());
  ASSERT_EQ(increment_0, schedule->programs->at(0)->path);
  ASSERT_EQ(increment_n, schedule->programs->at(1)->path);

  ASSERT_EQ(
    vector<word>({0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1}),
    schedule->scheduled);

  cout << schedule->print();
  */
}

// TODO: remove
#include <z3++.h>
TEST_F(Z3Test, DISABLED_api)
{
  using namespace z3;

  context c;

  expr heap = c.constant("heap", c.array_sort(c.bv_sort(16), c.bv_sort(16)));

  expr thread_0 = c.bool_const("thread_0");
  expr thread_1 = c.bool_const("thread_1");

  expr accu_0 = c.bv_const("accu_0", 16);
  expr accu_1 = c.bv_const("accu_1", 16);

  solver s(c);

  s.add((!thread_0 && thread_1) || (thread_0 && !thread_1));

  s.add(
    accu_0 ==
      ite(
        thread_0,
        c.bv_val(1, 16),
        c.bv_val(0, 16)));

  s.add(
    accu_1 ==
      ite(
        thread_1,
        c.bv_val(2, 16),
        c.bv_val(0, 16)));

  s.add(
    heap ==
      ite(
        thread_1,
        store(heap, c.bv_val(0, 16), accu_1),
        ite(
          thread_0,
          store(heap, c.bv_val(0, 16), accu_0),
          heap)));

  cout << s;

  cout << setfill('#') << setw(80) << eol;

  cout << s.check() << eol;

  cout << setfill('#') << setw(80) << eol;

  model m = s.get_model();
  cout << m << eol;

  cout << setfill('#') << setw(80) << eol;

  cout << m.eval(heap) << eol;

  if (m.eval(thread_0).is_true())
    cout << "accu_0 = " << m.eval(accu_0) << eol;
  else if (m.eval(thread_1).is_true())
    cout << "accu_1 = " << m.eval(accu_1) << eol;

  cout << "heap[0] = " << m.eval(select(heap, c.bv_val(0, 16))) << eol;

  cout << setfill('#') << setw(80) << eol;

  for (size_t i = 0; i < m.size(); ++i)
    cout << m[i].name().str() << " = " << m.eval(m[i]()) << eol;
}

// TODO: remove
TEST_F(Z3Test, DISABLED_api_parse)
{
  using namespace z3;

  // ifstream file("data/increment.cas.functional.t2.k12.smt2");
  // string formula((istreambuf_iterator<char>(file)),
                  // istreambuf_iterator<char>());

  unsigned long num_threads = 2;
  unsigned long bound = 12;

  context c;
  solver s {c};

  s.from_file("data/increment.cas.functional.t2.k12.smt2");

  expr_vector threads {c};

  for (unsigned long i = 1; i <= bound; ++i)
    for (unsigned long j = 0; j < num_threads; ++j)
      {
        ostringstream name;
        name << "thread_" << i << "_" << j;
        threads.push_back(c.bool_const(name.str().c_str()));
      }

  s.check();

  model m {s.get_model()};

  // cout << m << eol;

  cout << setfill('#') << setw(80) << eol;

  for (const expr & t : threads)
    cout << t.decl().name().str() << " = " << m.eval(t) << eol;
}
