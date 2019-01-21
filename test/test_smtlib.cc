#include <gtest/gtest.h>

#include "boolector.hh"
#include "smtlib.hh"
#include "streamredirecter.hh"

using namespace std;

/* word2hex *******************************************************************/
TEST(SMTLibTest, word2hex)
{
  ASSERT_EQ("#x0000", smtlib::word2hex(0));
  ASSERT_EQ("#x0001", smtlib::word2hex(1));
  ASSERT_EQ("#x000a", smtlib::word2hex(10));
  ASSERT_EQ("#x000f", smtlib::word2hex(15));
  ASSERT_EQ("#x0020", smtlib::word2hex(32));
}

/* expr ***********************************************************************/
TEST(SMTLibTest, expr)
{
  const char * expected = "(op x1 x2 x3)";

  ASSERT_EQ(expected, smtlib::expr("op", {"x1", "x2", "x3"}));
}

/* comment ******************************************************************/
TEST(SMTLibTest, comment)
{
  ASSERT_EQ("; foo", smtlib::comment("foo"));
}

/* comment section **********************************************************/
TEST(SMTLibTest, comment_section)
{
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; foo\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    smtlib::comment_section("foo"));
}

/* comment subsection *******************************************************/
TEST(SMTLibTest, comment_subsection)
{
  ASSERT_EQ(
    "; foo ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    smtlib::comment_subsection("foo"));
}

/* assertion ******************************************************************/
TEST(SMTLibTest, assert)
{
  const char * expected = "(assert true)";

  ASSERT_EQ(expected, smtlib::assertion("true"));
}

/* lnot ***********************************************************************/
TEST(SMTLibTest, lnot)
{
  const char * expected = "(not x1)";

  ASSERT_EQ(expected, smtlib::lnot("x1"));
}

/* lor ************************************************************************/
TEST(SMTLibTest, lor)
{
  const char * expected = "(or x1 x2 x3)";

  ASSERT_EQ(expected, smtlib::lor({"x1", "x2", "x3"}));
}

/* land ***********************************************************************/
TEST(SMTLibTest, land)
{
  const char * expected = "(and x1 x2 x3)";

  ASSERT_EQ(expected, smtlib::land({"x1", "x2", "x3"}));
}

/* implication ****************************************************************/
TEST(SMTLibTest, implication)
{
  const char * expected = "(=> x1 x2)";

  ASSERT_EQ(expected, smtlib::implication("x1", "x2"));
}

/* equality *******************************************************************/
TEST(SMTLibTest, equality)
{
  const char * expected = "(= x1 x2 x3)";

  ASSERT_EQ(expected, smtlib::equality({"x1", "x2", "x3"}));
}

/* if-then-else ***************************************************************/
TEST(SMTLibTest, ite)
{
  const char * expected = "(ite x1 x2 x3)";

  ASSERT_EQ(expected, smtlib::ite("x1", "x2", "x3"));
}

/* bvadd **********************************************************************/
TEST(SMTLibTest, bvadd)
{
  const char * expected = "(bvadd x1 x2 x3)";

  ASSERT_EQ(expected, smtlib::bvadd({"x1", "x2", "x3"}));
}

/* bvsub **********************************************************************/
TEST(SMTLibTest, bvsub)
{
  const char * expected = "(bvsub x1 x2 x3)";

  ASSERT_EQ(expected, smtlib::bvsub({"x1", "x2", "x3"}));
}

/* select *********************************************************************/
TEST(SMTLibTest, select)
{
  const char * expected = "(select array index)";

  ASSERT_EQ(expected, smtlib::select("array", "index"));
}

/* store **********************************************************************/
TEST(SMTLibTest, store)
{
  const char * expected = "(store array index value)";

  ASSERT_EQ(expected, smtlib::store("array", "index", "value"));
}

/* extract ********************************************************************/
TEST(SMTLibTest, extract)
{
  const char * expected = "((_ extract msb lsb) bv)";

  ASSERT_EQ(expected, smtlib::extract("msb", "lsb", "bv"));
}

/* bitvector ******************************************************************/
TEST(SMTLibTest, bitvector)
{
  const char * expected = "(_ BitVec 16)";

  ASSERT_EQ(expected, smtlib::bitvector(16));
}

/* array **********************************************************************/
TEST(SMTLibTest, array)
{
  const char * expected = "(Array (_ BitVec 16) (_ BitVec 16))";

  std::string bv = smtlib::bitvector(16);

  ASSERT_EQ(expected, smtlib::array(bv, bv));
}

/* declare_var ****************************************************************/
TEST(SMTLibTest, declare_var)
{
  const char * expected = "(declare-fun x1 () Bool)";

  ASSERT_EQ(expected, smtlib::declare_var("x1", "Bool"));
}

/* declare_bool_var ***********************************************************/
TEST(SMTLibTest, declare_bool_var)
{
  const char * expected = "(declare-fun x1 () Bool)";

  ASSERT_EQ(expected, smtlib::declare_bool_var("x1"));
}

/* declare_bv_var *************************************************************/
TEST(SMTLibTest, declare_bv_var)
{
  const char * expected = "(declare-fun x1 () (_ BitVec 16))";

  ASSERT_EQ(expected, smtlib::declare_bv_var("x1", 16));
}

/* declare_array_var **********************************************************/
TEST(SMTLibTest, declare_array_var)
{
  const string bv16 = smtlib::bitvector(16);
  const char * expected = "(declare-fun x1 () (Array (_ BitVec 16) (_ BitVec 16)))";

  ASSERT_EQ(expected, smtlib::declare_array_var("x1", bv16, bv16));
}

/* card_constraint_naive ******************************************************/
TEST(SMTLibTest, cardinality_exactly_one_naive)
{
  const char * expected;

  expected =
    "(assert (or x1 x2))\n"
    "(assert (or (not x1) (not x2)))\n";

  ASSERT_EQ(
    expected,
    smtlib::card_constraint_naive({"x1", "x2"}));

  expected =
    "(assert (or x1 x2 x3))\n"
    "(assert (or (not x1) (not x2)))\n"
    "(assert (or (not x1) (not x3)))\n"
    "(assert (or (not x2) (not x3)))\n";

  ASSERT_EQ(
    expected,
    smtlib::card_constraint_naive({"x1", "x2", "x3"}));

  expected =
    "(assert (or x1 x2 x3 x4))\n"
    "(assert (or (not x1) (not x2)))\n"
    "(assert (or (not x1) (not x3)))\n"
    "(assert (or (not x1) (not x4)))\n"
    "(assert (or (not x2) (not x3)))\n"
    "(assert (or (not x2) (not x4)))\n"
    "(assert (or (not x3) (not x4)))\n";

  ASSERT_EQ(
    expected,
    smtlib::card_constraint_naive({"x1", "x2", "x3", "x4"}));
}

TEST(SMTLibTest, cardinality_exactly_one_naive_verify)
{
  Boolector btor;

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  vector<string> vars({"x1", "x2", "x3"});

  string formula = smtlib::set_logic() + eol;

  for (const auto & v : vars)
    formula += smtlib::declare_bool_var(v) + eol;

  formula += smtlib::card_constraint_naive(vars);

  /* not none */
  string spec = formula;

  for (const auto & v : vars)
    spec += smtlib::assertion(smtlib::lnot(v)) + eol;

  spec += smtlib::check_sat() + eol;

  redirecter.start();

  ASSERT_FALSE(btor.sat(spec));

  redirecter.stop();

  /* not more than one */
  spec = formula;

  for (size_t i = 0; i < vars.size() - 1; i++)
    for (size_t j = i + 1; j < vars.size(); j++)
      spec += smtlib::assertion(smtlib::land({vars[i], vars[j]})) + eol;

  spec += smtlib::check_sat() + eol;

  redirecter.start();

  ASSERT_FALSE(btor.sat(spec));

  redirecter.stop();
}

/* card_constraint_sinz *******************************************************/
TEST(SMTLibTest, cardinality_exactly_one_sinz)
{
  const char * expected;

  expected =
    "(declare-fun x1_aux () Bool)\n"
    "\n"
    "(assert (or x1 x2))\n"

    "(assert (or (not x1) x1_aux))\n"
    "(assert (or (not x2) (not x1_aux)))\n";

  ASSERT_EQ(
    expected,
    smtlib::card_constraint_sinz({"x1", "x2"}));

  expected =
    "(declare-fun x1_aux () Bool)\n"
    "(declare-fun x2_aux () Bool)\n"
    "\n"
    "(assert (or x1 x2 x3))\n"

    "(assert (or (not x1) x1_aux))\n"
    "(assert (or (not x3) (not x2_aux)))\n"

    "(assert (or (not x2) x2_aux))\n"
    "(assert (or (not x1_aux) x2_aux))\n"
    "(assert (or (not x2) (not x1_aux)))\n";

  ASSERT_EQ(
    expected,
    smtlib::card_constraint_sinz({"x1", "x2", "x3"}));

  expected =
    "(declare-fun x1_aux () Bool)\n"
    "(declare-fun x2_aux () Bool)\n"
    "(declare-fun x3_aux () Bool)\n"
    "\n"
    "(assert (or x1 x2 x3 x4))\n"

    "(assert (or (not x1) x1_aux))\n"
    "(assert (or (not x4) (not x3_aux)))\n"

    "(assert (or (not x2) x2_aux))\n"
    "(assert (or (not x1_aux) x2_aux))\n"
    "(assert (or (not x2) (not x1_aux)))\n"

    "(assert (or (not x3) x3_aux))\n"
    "(assert (or (not x2_aux) x3_aux))\n"
    "(assert (or (not x3) (not x2_aux)))\n";

  ASSERT_EQ(
    expected,
    smtlib::card_constraint_sinz({"x1", "x2", "x3", "x4"}));
}

TEST(SMTLibTest, cardinality_exactly_one_sinz_verify)
{
  Boolector btor;

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  vector<string> vars({"x1", "x2", "x3", "x4", "x5", "x6"});

  string formula = smtlib::set_logic() + eol;

  for (const auto & v : vars)
    formula += smtlib::declare_bool_var(v) + eol;

  formula += smtlib::card_constraint_sinz(vars);

  /* not none */
  string spec = formula;

  for (const auto & v : vars)
    spec += smtlib::assertion(smtlib::lnot(v)) + eol;

  spec += smtlib::check_sat() + eol;

  redirecter.start();

  ASSERT_FALSE(btor.sat(spec));

  redirecter.stop();

  /* not more than one */
  spec = formula;

  for (size_t i = 0; i < vars.size() - 1; i++)
    for (size_t j = i + 1; j < vars.size(); j++)
      spec += smtlib::assertion(smtlib::land({vars[i], vars[j]})) + eol;

  spec += smtlib::check_sat() + eol;

  redirecter.start();

  ASSERT_FALSE(btor.sat(spec));

  redirecter.stop();
}
