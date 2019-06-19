#include <gtest/gtest.h>

#include "boolector.hh"
#include "smtlib.hh"
#include "streamredirecter.hh"

using namespace std;

/* word2hex *******************************************************************/
TEST(SMTLib_Test, word2hex)
{
  ASSERT_EQ("#x0000", smtlib::word2hex(0));
  ASSERT_EQ("#x0001", smtlib::word2hex(1));
  ASSERT_EQ("#x000a", smtlib::word2hex(10));
  ASSERT_EQ("#x000f", smtlib::word2hex(15));
  ASSERT_EQ("#x0020", smtlib::word2hex(32));
}

/* expr ***********************************************************************/
TEST(SMTLib_Test, expr)
{
  ASSERT_EQ("(op x1 x2 x3)", smtlib::expr("op", {"x1", "x2", "x3"}));
}

/* comment ******************************************************************/
TEST(SMTLib_Test, comment)
{
  ASSERT_EQ("; foo", smtlib::comment("foo"));
}

/* comment section **********************************************************/
TEST(SMTLib_Test, comment_section)
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
TEST(SMTLib_Test, comment_subsection)
{
  ASSERT_EQ(
    "; foo ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    smtlib::comment_subsection("foo"));
}

/* assertion ******************************************************************/
TEST(SMTLib_Test, assert)
{
  ASSERT_EQ("(assert true)", smtlib::assertion("true"));
}

/* lnot ***********************************************************************/
TEST(SMTLib_Test, lnot)
{
  ASSERT_EQ("(not x1)", smtlib::lnot("x1"));
}

/* land ***********************************************************************/
TEST(SMTLib_Test, land)
{
  ASSERT_THROW(smtlib::land({}), runtime_error);

  ASSERT_EQ("x1", smtlib::land({"x1"}));

  ASSERT_EQ("(and x1 x2 x3)", smtlib::land({"x1", "x2", "x3"}));
}

/* lor ************************************************************************/
TEST(SMTLib_Test, lor)
{
  ASSERT_THROW(smtlib::lor({}), runtime_error);

  ASSERT_EQ("x1", smtlib::lor({"x1"}));

  ASSERT_EQ("(or x1 x2 x3)", smtlib::lor({"x1", "x2", "x3"}));
}

/* lxor ***********************************************************************/
TEST(SMTLib_Test, lxor)
{
  ASSERT_THROW(smtlib::lxor({}), runtime_error);

  ASSERT_EQ("x1", smtlib::lxor({"x1"}));

  ASSERT_EQ("(xor x1 x2 x3)", smtlib::lxor({"x1", "x2", "x3"}));
}

/* implication ****************************************************************/
TEST(SMTLib_Test, implication)
{
  ASSERT_EQ("(=> x1 x2)", smtlib::implication("x1", "x2"));
}

/* equality *******************************************************************/
TEST(SMTLib_Test, equality)
{
  ASSERT_THROW(smtlib::equality({}), runtime_error);

  ASSERT_THROW(smtlib::equality({"x1"}), runtime_error);

  ASSERT_EQ("(= x1 x2 x3)", smtlib::equality({"x1", "x2", "x3"}));
}

/* if-then-else ***************************************************************/
TEST(SMTLib_Test, ite)
{
  ASSERT_EQ("(ite x1 x2 x3)", smtlib::ite("x1", "x2", "x3"));
}

/* bvadd **********************************************************************/
TEST(SMTLib_Test, bvadd)
{
  ASSERT_THROW(smtlib::bvadd({}), runtime_error);

  ASSERT_THROW(smtlib::bvadd({"x1"}), runtime_error);

  ASSERT_EQ("(bvadd x1 x2 x3)", smtlib::bvadd({"x1", "x2", "x3"}));
}

/* bvsub **********************************************************************/
TEST(SMTLib_Test, bvsub)
{
  ASSERT_THROW(smtlib::bvsub({}), runtime_error);

  ASSERT_THROW(smtlib::bvsub({"x1"}), runtime_error);

  ASSERT_EQ("(bvsub x1 x2 x3)", smtlib::bvsub({"x1", "x2", "x3"}));
}

/* select *********************************************************************/
TEST(SMTLib_Test, select)
{
  ASSERT_EQ("(select array index)", smtlib::select("array", "index"));
}

/* store **********************************************************************/
TEST(SMTLib_Test, store)
{
  ASSERT_EQ(
    "(store array index value)",
    smtlib::store("array", "index", "value"));
}

/* extract ********************************************************************/
TEST(SMTLib_Test, extract)
{
  ASSERT_EQ("((_ extract msb lsb) bv)", smtlib::extract("msb", "lsb", "bv"));
}

/* bitvector ******************************************************************/
TEST(SMTLib_Test, bitvector)
{
  ASSERT_EQ("(_ BitVec 16)", smtlib::bitvector(16));
}

/* array **********************************************************************/
TEST(SMTLib_Test, array)
{
  std::string bv = smtlib::bitvector(16);

  ASSERT_EQ("(Array (_ BitVec 16) (_ BitVec 16))", smtlib::array(bv, bv));
}

/* declare_var ****************************************************************/
TEST(SMTLib_Test, declare_var)
{
  ASSERT_EQ("(declare-fun x1 () Bool)", smtlib::declare_var("x1", "Bool"));
}

/* declare_bool_var ***********************************************************/
TEST(SMTLib_Test, declare_bool_var)
{
  ASSERT_EQ("(declare-fun x1 () Bool)", smtlib::declare_bool_var("x1"));
}

/* declare_bv_var *************************************************************/
TEST(SMTLib_Test, declare_bv_var)
{
  ASSERT_EQ(
    "(declare-fun x1 () (_ BitVec 16))",
    smtlib::declare_bv_var("x1", 16));
}

/* declare_array_var **********************************************************/
TEST(SMTLib_Test, declare_array_var)
{
  const string bv16 = smtlib::bitvector(16);

  ASSERT_EQ(
    "(declare-fun x1 () (Array (_ BitVec 16) (_ BitVec 16)))",
    smtlib::declare_array_var("x1", bv16, bv16));
}

/* card_constraint_naive ******************************************************/
TEST(SMTLib_Test, cardinality_exactly_one_naive)
{
  ASSERT_THROW(smtlib::card_constraint_naive({}), runtime_error);

  ASSERT_EQ("(assert x1)\n", smtlib::card_constraint_naive({"x1"}));

  ASSERT_EQ(
    "(assert (xor x1 x2))\n",
    smtlib::card_constraint_naive({"x1", "x2"}));

  ASSERT_EQ(
    "(assert (or x1 x2 x3))\n"
    "(assert (or (not x1) (not x2)))\n"
    "(assert (or (not x1) (not x3)))\n"
    "(assert (or (not x2) (not x3)))\n",
    smtlib::card_constraint_naive({"x1", "x2", "x3"}));

  ASSERT_EQ(
    "(assert (or x1 x2 x3 x4))\n"
    "(assert (or (not x1) (not x2)))\n"
    "(assert (or (not x1) (not x3)))\n"
    "(assert (or (not x1) (not x4)))\n"
    "(assert (or (not x2) (not x3)))\n"
    "(assert (or (not x2) (not x4)))\n"
    "(assert (or (not x3) (not x4)))\n",
    smtlib::card_constraint_naive({"x1", "x2", "x3", "x4"}));
}

TEST(SMTLib_Test, cardinality_exactly_one_naive_verify)
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
TEST(SMTLib_Test, cardinality_exactly_one_sinz)
{
  ASSERT_THROW(smtlib::card_constraint_sinz({}), runtime_error);

  ASSERT_EQ("(assert x1)\n", smtlib::card_constraint_sinz({"x1"}));

  ASSERT_EQ(
    "(assert (xor x1 x2))\n",
    smtlib::card_constraint_sinz({"x1", "x2"}));

  ASSERT_EQ(
    "(declare-fun x1_aux () Bool)\n"
    "(declare-fun x2_aux () Bool)\n"
    "\n"
    "(assert (or x1 x2 x3))\n"

    "(assert (or (not x1) x1_aux))\n"
    "(assert (or (not x3) (not x2_aux)))\n"

    "(assert (or (not x2) x2_aux))\n"
    "(assert (or (not x1_aux) x2_aux))\n"
    "(assert (or (not x2) (not x1_aux)))\n",
    smtlib::card_constraint_sinz({"x1", "x2", "x3"}));

  ASSERT_EQ(
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
    "(assert (or (not x3) (not x2_aux)))\n",
    smtlib::card_constraint_sinz({"x1", "x2", "x3", "x4"}));
}

TEST(SMTLib_Test, cardinality_exactly_one_sinz_verify)
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
