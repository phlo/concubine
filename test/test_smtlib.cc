#include <gtest/gtest.h>

#include "boolector.hh"
#include "smtlib.hh"

namespace ConcuBinE::test {

//==============================================================================
// SMT-Lib v2.5 std::string generator tests
//==============================================================================

// word2hex ====================================================================

  TEST(smtlib, word2hex)
{
  ASSERT_EQ("#x0000", smtlib::word2hex(0));
  ASSERT_EQ("#x0001", smtlib::word2hex(1));
  ASSERT_EQ("#x000a", smtlib::word2hex(10));
  ASSERT_EQ("#x000f", smtlib::word2hex(15));
  ASSERT_EQ("#x0020", smtlib::word2hex(32));
}

// expr ========================================================================

TEST(smtlib, expr)
{
  ASSERT_EQ("(op x1 x2 x3)", smtlib::expr("op", {"x1", "x2", "x3"}));
}

// comment =====================================================================

TEST(smtlib, comment)
{
  ASSERT_EQ("; foo", smtlib::comment("foo"));
}

// comment_section =============================================================

TEST(smtlib, comment_section)
{
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; foo\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    smtlib::comment_section("foo"));
}

// comment_subsection ==========================================================

TEST(smtlib, comment_subsection)
{
  ASSERT_EQ(
    "; foo ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    smtlib::comment_subsection("foo"));
}

// assert ======================================================================

TEST(smtlib, assert)
{
  ASSERT_EQ("(assert true)", smtlib::assertion("true"));
}

// lnot ========================================================================

TEST(smtlib, lnot)
{
  ASSERT_EQ("(not x1)", smtlib::lnot("x1"));
}

// land ========================================================================

TEST(smtlib, land)
{
  ASSERT_THROW(smtlib::land({}), std::runtime_error);

  ASSERT_EQ("x1", smtlib::land({"x1"}));

  ASSERT_EQ("(and x1 x2 x3)", smtlib::land({"x1", "x2", "x3"}));
}

// lor =========================================================================

TEST(smtlib, lor)
{
  ASSERT_THROW(smtlib::lor({}), std::runtime_error);

  ASSERT_EQ("x1", smtlib::lor({"x1"}));

  ASSERT_EQ("(or x1 x2 x3)", smtlib::lor({"x1", "x2", "x3"}));
}

// lxor ========================================================================

TEST(smtlib, lxor)
{
  ASSERT_THROW(smtlib::lxor({}), std::runtime_error);

  ASSERT_EQ("x1", smtlib::lxor({"x1"}));

  ASSERT_EQ("(xor x1 x2 x3)", smtlib::lxor({"x1", "x2", "x3"}));
}

// implication =================================================================

TEST(smtlib, implication)
{
  ASSERT_EQ("(=> x1 x2)", smtlib::implication("x1", "x2"));
}

// equality ====================================================================

TEST(smtlib, equality)
{
  ASSERT_THROW(smtlib::equality({}), std::runtime_error);

  ASSERT_THROW(smtlib::equality({"x1"}), std::runtime_error);

  ASSERT_EQ("(= x1 x2 x3)", smtlib::equality({"x1", "x2", "x3"}));
}

// ite =========================================================================

TEST(smtlib, ite)
{
  ASSERT_EQ("(ite x1 x2 x3)", smtlib::ite("x1", "x2", "x3"));
}

// bvadd =======================================================================

TEST(smtlib, bvadd)
{
  ASSERT_THROW(smtlib::bvadd({}), std::runtime_error);

  ASSERT_THROW(smtlib::bvadd({"x1"}), std::runtime_error);

  ASSERT_EQ("(bvadd x1 x2 x3)", smtlib::bvadd({"x1", "x2", "x3"}));
}

// bvsub =======================================================================

TEST(smtlib, bvsub)
{
  ASSERT_THROW(smtlib::bvsub({}), std::runtime_error);

  ASSERT_THROW(smtlib::bvsub({"x1"}), std::runtime_error);

  ASSERT_EQ("(bvsub x1 x2 x3)", smtlib::bvsub({"x1", "x2", "x3"}));
}

// bvmul =======================================================================

TEST(smtlib, bvmul)
{
  ASSERT_THROW(smtlib::bvmul({}), std::runtime_error);

  ASSERT_THROW(smtlib::bvmul({"x1"}), std::runtime_error);

  ASSERT_EQ("(bvmul x1 x2 x3)", smtlib::bvmul({"x1", "x2", "x3"}));
}

// select ======================================================================

TEST(smtlib, select)
{
  ASSERT_EQ("(select array index)", smtlib::select("array", "index"));
}

// store =======================================================================

TEST(smtlib, store)
{
  ASSERT_EQ(
    "(store array index value)",
    smtlib::store("array", "index", "value"));
}

// extract =====================================================================

TEST(smtlib, extract)
{
  ASSERT_EQ("((_ extract msb lsb) bv)", smtlib::extract("msb", "lsb", "bv"));
}

// bitvector ===================================================================

TEST(smtlib, bitvector)
{
  ASSERT_EQ("(_ BitVec 16)", smtlib::bitvector(16));
}

// array =======================================================================

TEST(smtlib, array)
{
  const std::string bv = smtlib::bitvector(16);

  ASSERT_EQ("(Array (_ BitVec 16) (_ BitVec 16))", smtlib::array(bv, bv));
}

// declare_var =================================================================

TEST(smtlib, declare_var)
{
  ASSERT_EQ("(declare-fun x1 () Bool)", smtlib::declare_var("x1", "Bool"));
}

// declare_bool_var ============================================================

TEST(smtlib, declare_bool_var)
{
  ASSERT_EQ("(declare-fun x1 () Bool)", smtlib::declare_bool_var("x1"));
}

// declare_bv_var ==============================================================

TEST(smtlib, declare_bv_var)
{
  ASSERT_EQ(
    "(declare-fun x1 () (_ BitVec 16))",
    smtlib::declare_bv_var("x1", 16));
}

// declare_array_var ===========================================================

TEST(smtlib, declare_array_var)
{
  const std::string bv16 = smtlib::bitvector(16);

  ASSERT_EQ(
    "(declare-fun x1 () (Array (_ BitVec 16) (_ BitVec 16)))",
    smtlib::declare_array_var("x1", bv16, bv16));
}

// card_constraint_naive =======================================================

TEST(smtlib, cardinality_exactly_one_naive)
{
  ASSERT_THROW(smtlib::card_constraint_naive({}), std::runtime_error);

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

TEST(smtlib, cardinality_exactly_one_naive_verify)
{
  Boolector btor;
  std::ostringstream ss;
  std::vector<std::string> vars({"x1", "x2", "x3"});
  std::string formula = smtlib::set_logic() + eol;

  for (const auto & v : vars)
    formula += smtlib::declare_bool_var(v) + eol;

  formula += smtlib::card_constraint_naive(vars);

  // not none
  std::string spec = formula;

  for (const auto & v : vars)
    spec += smtlib::assertion(smtlib::lnot(v)) + eol;

  spec += smtlib::check_sat() + eol;

  ASSERT_FALSE(btor.sat(spec));

  // not more than one
  spec = formula;

  for (size_t i = 0; i < vars.size() - 1; i++)
    for (size_t j = i + 1; j < vars.size(); j++)
      spec += smtlib::assertion(smtlib::land({vars[i], vars[j]})) + eol;

  spec += smtlib::check_sat() + eol;

  ASSERT_FALSE(btor.sat(spec));
}

// card_constraint_sinz ========================================================

TEST(smtlib, cardinality_exactly_one_sinz)
{
  ASSERT_THROW(smtlib::card_constraint_sinz({}), std::runtime_error);

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

TEST(smtlib, cardinality_exactly_one_sinz_verify)
{
  Boolector btor;
  std::ostringstream ss;
  std::vector<std::string> vars({"x1", "x2", "x3", "x4", "x5", "x6"});
  std::string formula = smtlib::set_logic() + eol;

  for (const auto & v : vars)
    formula += smtlib::declare_bool_var(v) + eol;

  formula += smtlib::card_constraint_sinz(vars);

  // not none
  std::string spec = formula;

  for (const auto & v : vars)
    spec += smtlib::assertion(smtlib::lnot(v)) + eol;

  spec += smtlib::check_sat() + eol;

  ASSERT_FALSE(btor.sat(spec));

  // not more than one
  spec = formula;

  for (size_t i = 0; i < vars.size() - 1; i++)
    for (size_t j = i + 1; j < vars.size(); j++)
      spec += smtlib::assertion(smtlib::land({vars[i], vars[j]})) + eol;

  spec += smtlib::check_sat() + eol;

  ASSERT_FALSE(btor.sat(spec));
}

} // namespace ConcuBinE::test
