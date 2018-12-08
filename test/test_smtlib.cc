#include <gtest/gtest.h>

#include "smtlib.hh"

using namespace std;

/* word2hex *******************************************************************/
TEST(SMTLibTest, word2hex)
{
  ASSERT_STREQ("#x0000", smtlib::word2hex(0).c_str());
  ASSERT_STREQ("#x0001", smtlib::word2hex(1).c_str());
  ASSERT_STREQ("#x000a", smtlib::word2hex(10).c_str());
  ASSERT_STREQ("#x000f", smtlib::word2hex(15).c_str());
  ASSERT_STREQ("#x0020", smtlib::word2hex(32).c_str());
}

/* expr ***********************************************************************/
TEST(SMTLibTest, expr)
{
  const char * expected = "(op x1 x2 x3)";

  ASSERT_STREQ(expected, smtlib::expr("op", {"x1", "x2", "x3"}).c_str());
}

/* assertion ******************************************************************/
TEST(SMTLibTest, assert)
{
  const char * expected = "(assert true)";

  ASSERT_STREQ(expected, smtlib::assertion("true").c_str());
}

/* lnot ***********************************************************************/
TEST(SMTLibTest, lnot)
{
  const char * expected = "(not x1)";

  ASSERT_STREQ(expected, smtlib::lnot("x1").c_str());
}

/* lor ************************************************************************/
TEST(SMTLibTest, lor)
{
  const char * expected = "(or x1 x2 x3)";

  ASSERT_STREQ(expected, smtlib::lor({"x1", "x2", "x3"}).c_str());
}

/* land ***********************************************************************/
TEST(SMTLibTest, land)
{
  const char * expected = "(and x1 x2 x3)";

  ASSERT_STREQ(expected, smtlib::land({"x1", "x2", "x3"}).c_str());
}

/* implication ****************************************************************/
TEST(SMTLibTest, implication)
{
  const char * expected = "(=> x1 x2)";

  ASSERT_STREQ(expected, smtlib::implication("x1", "x2").c_str());
}

/* equality *******************************************************************/
TEST(SMTLibTest, equality)
{
  const char * expected = "(= x1 x2 x3)";

  ASSERT_STREQ(expected, smtlib::equality({"x1", "x2", "x3"}).c_str());
}

/* bvadd **********************************************************************/
TEST(SMTLibTest, bvadd)
{
  const char * expected = "(bvadd x1 x2 x3)";

  ASSERT_STREQ(expected, smtlib::bvadd({"x1", "x2", "x3"}).c_str());
}

/* bvsub **********************************************************************/
TEST(SMTLibTest, bvsub)
{
  const char * expected = "(bvsub x1 x2 x3)";

  ASSERT_STREQ(expected, smtlib::bvsub({"x1", "x2", "x3"}).c_str());
}

/* select *********************************************************************/
TEST(SMTLibTest, select)
{
  const char * expected = "(select array index)";

  ASSERT_STREQ(expected, smtlib::select("array", "index").c_str());
}

/* store **********************************************************************/
TEST(SMTLibTest, store)
{
  const char * expected = "(store array index value)";

  ASSERT_STREQ(expected, smtlib::store("array", "index", "value").c_str());
}

/* extract ********************************************************************/
TEST(SMTLibTest, extract)
{
  const char * expected = "((_ extract msb lsb) bv)";

  ASSERT_STREQ(expected, smtlib::extract("msb", "lsb", "bv").c_str());
}

/* declareVar *****************************************************************/
TEST(SMTLibTest, declareVar)
{
  const char * expected = "(declare-fun x1 () Bool)";

  ASSERT_STREQ(expected, smtlib::declareVar("x1", "Bool").c_str());
}

/* bitvector ******************************************************************/
TEST(SMTLibTest, bitvector)
{
  const char * expected = "(_ BitVec 16)";

  ASSERT_STREQ(expected, smtlib::bitvector("16").c_str());
}

/* array **********************************************************************/
TEST(SMTLibTest, array)
{
  const char * expected = "(Array (_ BitVec 16) (_ BitVec 16))";

  std::string bv = smtlib::bitvector("16");

  ASSERT_STREQ(expected, smtlib::array(bv, bv).c_str());
}

/* card_constraint_naive ******************************************************/
TEST(SMTLibTest, cardinality_exactly_one_naive)
{
  const char * expected;

  expected = "(assert (or (not x1) (not x2)))\n";

  ASSERT_STREQ(
    expected,
    smtlib::card_constraint_naive({"x1", "x2"}).c_str());

  expected =
    "(assert (or (not x1) (not x2)))\n"
    "(assert (or (not x1) (not x3)))\n"
    "(assert (or (not x2) (not x3)))\n";

  ASSERT_STREQ(
    expected,
    smtlib::card_constraint_naive({"x1", "x2", "x3"}).c_str());

  expected =
    "(assert (or (not x1) (not x2)))\n"
    "(assert (or (not x1) (not x3)))\n"
    "(assert (or (not x1) (not x4)))\n"
    "(assert (or (not x2) (not x3)))\n"
    "(assert (or (not x2) (not x4)))\n"
    "(assert (or (not x3) (not x4)))\n";

  ASSERT_STREQ(
    expected,
    smtlib::card_constraint_naive({"x1", "x2", "x3", "x4"}).c_str());
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

  ASSERT_STREQ(
    expected,
    smtlib::card_constraint_sinz({"x1", "x2"}).c_str());

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

  ASSERT_STREQ(
    expected,
    smtlib::card_constraint_sinz({"x1", "x2", "x3"}).c_str());

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

  ASSERT_STREQ(
    expected,
    smtlib::card_constraint_sinz({"x1", "x2", "x3", "x4"}).c_str());
}