#include <gtest/gtest.h>

#include "btor2.hh"
#include "btormc.hh"

namespace test {

//==============================================================================
// BTOR2 std::string generator tests
//==============================================================================

// comment =====================================================================

TEST(btor2, comment)
{
  ASSERT_EQ("; foo", btor2::comment("foo"));
}

// comment_section =============================================================

TEST(btor2, comment_section)
{
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; foo\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    btor2::comment_section("foo"));
}

// comment_subsection ==========================================================

TEST(btor2, comment_subsection)
{
  ASSERT_EQ(
    "; foo ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    btor2::comment_subsection("foo"));
}

// declare_sort ================================================================

TEST(btor2, declare_sort)
{
  ASSERT_EQ("1 sort bitvec 1\n", btor2::declare_sort("1", "1"));
  ASSERT_EQ("2 sort bitvec 16\n", btor2::declare_sort("2", "16"));
  ASSERT_EQ("3 sort bitvec 32 foo\n", btor2::declare_sort("3", "32", "foo"));
}

// declare_array ===============================================================

TEST(btor2, declare_array)
{
  ASSERT_EQ("1 sort array 2 2\n", btor2::declare_array("1", "2", "2"));
  ASSERT_EQ("2 sort array 16 16\n", btor2::declare_array("2", "16", "16"));
  ASSERT_EQ(
    "3 sort array 32 32 foo\n",
    btor2::declare_array("3", "32", "32", "foo"));
}

// constd ======================================================================

TEST(btor2, constd)
{
  ASSERT_EQ("12 constd 2 2\n", btor2::constd("12", "2", "2"));
  ASSERT_EQ("13 constd 3 3\n", btor2::constd("13", "3", "3"));
  ASSERT_EQ("14 constd 4 4 foo\n", btor2::constd("14", "4", "4", "foo"));

  // zero one
  ASSERT_EQ("1 zero 1\n", btor2::constd("1", "1", "0"));
  ASSERT_EQ("2 one 1\n", btor2::constd("2", "1", "1"));
}

// input =======================================================================

TEST(btor2, input)
{
  ASSERT_EQ("11 input 1\n", btor2::input("11", "1"));
  ASSERT_EQ("12 input 2\n", btor2::input("12", "2"));
  ASSERT_EQ("13 input 3 foo\n", btor2::input("13", "3", "foo"));
}

// state =======================================================================

TEST(btor2, state)
{
  ASSERT_EQ("11 state 1\n", btor2::state("11", "1"));
  ASSERT_EQ("12 state 2\n", btor2::state("12", "2"));
  ASSERT_EQ("13 state 3 foo\n", btor2::state("13", "3", "foo"));
}

// init ========================================================================

TEST(btor2, init)
{
  ASSERT_EQ("11 init 1 2 3\n", btor2::init("11", "1", "2", "3"));
  ASSERT_EQ("12 init 4 5 6\n", btor2::init("12", "4", "5", "6"));
  ASSERT_EQ("13 init 7 8 9 foo\n", btor2::init("13", "7", "8", "9", "foo"));
}

// next ========================================================================

TEST(btor2, next)
{
  ASSERT_EQ("11 next 1 2 3\n", btor2::next("11", "1", "2", "3"));
  ASSERT_EQ("12 next 4 5 6\n", btor2::next("12", "4", "5", "6"));
  ASSERT_EQ("13 next 7 8 9 foo\n", btor2::next("13", "7", "8", "9", "foo"));
}

// constraint ==================================================================

TEST(btor2, constraint)
{
  ASSERT_EQ("11 constraint 1\n", btor2::constraint("11", "1"));
  ASSERT_EQ("12 constraint 2\n", btor2::constraint("12", "2"));
  ASSERT_EQ("13 constraint 3 foo\n", btor2::constraint("13", "3", "foo"));
}

TEST(btor2, constraint_prev)
{
  btor2::nid_t nid = 11;

  ASSERT_EQ("11 constraint 10\n", btor2::constraint(nid));
  ASSERT_EQ(12, nid);

  ASSERT_EQ("12 constraint 11\n", btor2::constraint(nid));
  ASSERT_EQ(13, nid);

  ASSERT_EQ("13 constraint 12 foo\n", btor2::constraint(nid, "foo"));
  ASSERT_EQ(14, nid);
}

// bad =========================================================================

TEST(btor2, bad)
{
  ASSERT_EQ("11 bad 1\n", btor2::bad("11", "1"));
  ASSERT_EQ("12 bad 2\n", btor2::bad("12", "2"));
  ASSERT_EQ("13 bad 3 foo\n", btor2::bad("13", "3", "foo"));
}

TEST(btor2, bad_prev)
{
  btor2::nid_t nid = 11;

  ASSERT_EQ("11 bad 10\n", btor2::bad(nid));
  ASSERT_EQ(12, nid);

  ASSERT_EQ("12 bad 11\n", btor2::bad(nid));
  ASSERT_EQ(13, nid);

  ASSERT_EQ("13 bad 12 foo\n", btor2::bad(nid, "foo"));
  ASSERT_EQ(14, nid);
}

// fair ========================================================================

TEST(btor2, fair)
{
  ASSERT_EQ("11 fair 1\n", btor2::fair("11", "1"));
  ASSERT_EQ("12 fair 2\n", btor2::fair("12", "2"));
  ASSERT_EQ("13 fair 3 foo\n", btor2::fair("13", "3", "foo"));
}

// output ======================================================================

TEST(btor2, output)
{
  ASSERT_EQ("11 output 1\n", btor2::output("11", "1"));
  ASSERT_EQ("12 output 2\n", btor2::output("12", "2"));
  ASSERT_EQ("13 output 3 foo\n", btor2::output("13", "3", "foo"));
}

// justice =====================================================================

TEST(btor2, justice)
{
  ASSERT_EQ("11 justice 1 1\n", btor2::justice("11", "1", {"1"}));
  ASSERT_EQ("12 justice 2 1 2\n", btor2::justice("12", "2", {"1", "2"}));
  ASSERT_EQ(
    "13 justice 3 1 2 3 foo\n",
    btor2::justice("13", "3", {"1", "2", "3"}, "foo"));
}

// sext ========================================================================

TEST(btor2, sext)
{
  ASSERT_EQ("11 sext 1 2 3\n", btor2::sext("11", "1", "2", "3"));
  ASSERT_EQ("12 sext 2 3 4\n", btor2::sext("12", "2", "3", "4"));
  ASSERT_EQ("13 sext 3 4 5 foo\n", btor2::sext("13", "3", "4", "5", "foo"));
}

// uext ========================================================================

TEST(btor2, uext)
{
  ASSERT_EQ("11 uext 1 2 3\n", btor2::uext("11", "1", "2", "3"));
  ASSERT_EQ("12 uext 2 3 4\n", btor2::uext("12", "2", "3", "4"));
  ASSERT_EQ("13 uext 3 4 5 foo\n", btor2::uext("13", "3", "4", "5", "foo"));
}

// slice =======================================================================

TEST(btor2, slice)
{
  ASSERT_EQ("11 slice 1 3 2 3\n", btor2::slice("11", "1", "3", "2", "3"));
  ASSERT_EQ("12 slice 2 4 3 4\n", btor2::slice("12", "2", "4", "3", "4"));
  ASSERT_EQ(
    "13 slice 3 5 4 5 foo\n",
    btor2::slice("13", "3", "5", "4", "5", "foo"));
}

// lnot ========================================================================

TEST(btor2, lnot)
{
  ASSERT_EQ("11 not 1 2\n", btor2::lnot("11", "1", "2"));
  ASSERT_EQ("12 not 2 3\n", btor2::lnot("12", "2", "3"));
  ASSERT_EQ("13 not 3 4 foo\n", btor2::lnot("13", "3", "4", "foo"));
}

// inc =========================================================================

TEST(btor2, inc)
{
  ASSERT_EQ("11 inc 1 2\n", btor2::inc("11", "1", "2"));
  ASSERT_EQ("12 inc 2 3\n", btor2::inc("12", "2", "3"));
  ASSERT_EQ("13 inc 3 4 foo\n", btor2::inc("13", "3", "4", "foo"));
}

// dec =========================================================================

TEST(btor2, dec)
{
  ASSERT_EQ("11 dec 1 2\n", btor2::dec("11", "1", "2"));
  ASSERT_EQ("12 dec 2 3\n", btor2::dec("12", "2", "3"));
  ASSERT_EQ("13 dec 3 4 foo\n", btor2::dec("13", "3", "4", "foo"));
}

// neg =========================================================================

TEST(btor2, neg)
{
  ASSERT_EQ("11 neg 1 2\n", btor2::neg("11", "1", "2"));
  ASSERT_EQ("12 neg 2 3\n", btor2::neg("12", "2", "3"));
  ASSERT_EQ("13 neg 3 4 foo\n", btor2::neg("13", "3", "4", "foo"));
}

// redand ======================================================================

TEST(btor2, redand)
{
  ASSERT_EQ("11 redand 1 2\n", btor2::redand("11", "1", "2"));
  ASSERT_EQ("12 redand 2 3\n", btor2::redand("12", "2", "3"));
  ASSERT_EQ("13 redand 3 4 foo\n", btor2::redand("13", "3", "4", "foo"));
}

// redor =======================================================================

TEST(btor2, redor)
{
  ASSERT_EQ("11 redor 1 2\n", btor2::redor("11", "1", "2"));
  ASSERT_EQ("12 redor 2 3\n", btor2::redor("12", "2", "3"));
  ASSERT_EQ("13 redor 3 4 foo\n", btor2::redor("13", "3", "4", "foo"));
}

// redxor ======================================================================

TEST(btor2, redxor)
{
  ASSERT_EQ("11 redxor 1 2\n", btor2::redxor("11", "1", "2"));
  ASSERT_EQ("12 redxor 2 3\n", btor2::redxor("12", "2", "3"));
  ASSERT_EQ("13 redxor 3 4 foo\n", btor2::redxor("13", "3", "4", "foo"));
}

// iff =========================================================================

TEST(btor2, iff)
{
  ASSERT_EQ("11 iff 1 2 3\n", btor2::iff("11", "1", "2", "3"));
  ASSERT_EQ("12 iff 2 3 4\n", btor2::iff("12", "2", "3", "4"));
  ASSERT_EQ("13 iff 3 4 5 foo\n", btor2::iff("13", "3", "4", "5", "foo"));
}

// implies =====================================================================

TEST(btor2, implies)
{
  ASSERT_EQ("11 implies 1 2 3\n", btor2::implies("11", "1", "2", "3"));
  ASSERT_EQ("12 implies 2 3 4\n", btor2::implies("12", "2", "3", "4"));
  ASSERT_EQ(
    "13 implies 3 4 5 foo\n",
    btor2::implies("13", "3", "4", "5", "foo"));
}

// eq ==========================================================================

TEST(btor2, eq)
{
  ASSERT_EQ("11 eq 1 2 3\n", btor2::eq("11", "1", "2", "3"));
  ASSERT_EQ("12 eq 2 3 4\n", btor2::eq("12", "2", "3", "4"));
  ASSERT_EQ("13 eq 3 4 5 foo\n", btor2::eq("13", "3", "4", "5", "foo"));
}

// ne ==========================================================================

TEST(btor2, ne)
{
  ASSERT_EQ("11 ne 1 2 3\n", btor2::ne("11", "1", "2", "3"));
  ASSERT_EQ("12 ne 2 3 4\n", btor2::ne("12", "2", "3", "4"));
  ASSERT_EQ("13 ne 3 4 5 foo\n", btor2::ne("13", "3", "4", "5", "foo"));
}

// sgt =========================================================================

TEST(btor2, sgt)
{
  ASSERT_EQ("11 sgt 1 2 3\n", btor2::sgt("11", "1", "2", "3"));
  ASSERT_EQ("12 sgt 2 3 4\n", btor2::sgt("12", "2", "3", "4"));
  ASSERT_EQ("13 sgt 3 4 5 foo\n", btor2::sgt("13", "3", "4", "5", "foo"));
}

// ugt =========================================================================

TEST(btor2, ugt)
{
  ASSERT_EQ("11 ugt 1 2 3\n", btor2::ugt("11", "1", "2", "3"));
  ASSERT_EQ("12 ugt 2 3 4\n", btor2::ugt("12", "2", "3", "4"));
  ASSERT_EQ("13 ugt 3 4 5 foo\n", btor2::ugt("13", "3", "4", "5", "foo"));
}

// sgte ========================================================================

TEST(btor2, sgte)
{
  ASSERT_EQ("11 sgte 1 2 3\n", btor2::sgte("11", "1", "2", "3"));
  ASSERT_EQ("12 sgte 2 3 4\n", btor2::sgte("12", "2", "3", "4"));
  ASSERT_EQ("13 sgte 3 4 5 foo\n", btor2::sgte("13", "3", "4", "5", "foo"));
}

// ugte ========================================================================

TEST(btor2, ugte)
{
  ASSERT_EQ("11 ugte 1 2 3\n", btor2::ugte("11", "1", "2", "3"));
  ASSERT_EQ("12 ugte 2 3 4\n", btor2::ugte("12", "2", "3", "4"));
  ASSERT_EQ("13 ugte 3 4 5 foo\n", btor2::ugte("13", "3", "4", "5", "foo"));
}

// slt =========================================================================

TEST(btor2, slt)
{
  ASSERT_EQ("11 slt 1 2 3\n", btor2::slt("11", "1", "2", "3"));
  ASSERT_EQ("12 slt 2 3 4\n", btor2::slt("12", "2", "3", "4"));
  ASSERT_EQ("13 slt 3 4 5 foo\n", btor2::slt("13", "3", "4", "5", "foo"));
}

// ult =========================================================================

TEST(btor2, ult)
{
  ASSERT_EQ("11 ult 1 2 3\n", btor2::ult("11", "1", "2", "3"));
  ASSERT_EQ("12 ult 2 3 4\n", btor2::ult("12", "2", "3", "4"));
  ASSERT_EQ("13 ult 3 4 5 foo\n", btor2::ult("13", "3", "4", "5", "foo"));
}

// slte ========================================================================

TEST(btor2, slte)
{
  ASSERT_EQ("11 slte 1 2 3\n", btor2::slte("11", "1", "2", "3"));
  ASSERT_EQ("12 slte 2 3 4\n", btor2::slte("12", "2", "3", "4"));
  ASSERT_EQ("13 slte 3 4 5 foo\n", btor2::slte("13", "3", "4", "5", "foo"));
}

// ulte ========================================================================

TEST(btor2, ulte)
{
  ASSERT_EQ("11 ulte 1 2 3\n", btor2::ulte("11", "1", "2", "3"));
  ASSERT_EQ("12 ulte 2 3 4\n", btor2::ulte("12", "2", "3", "4"));
  ASSERT_EQ("13 ulte 3 4 5 foo\n", btor2::ulte("13", "3", "4", "5", "foo"));
}

// land ========================================================================

TEST(btor2, land)
{
  ASSERT_EQ("11 and 1 2 3\n", btor2::land("11", "1", "2", "3"));
  ASSERT_EQ("12 and 2 3 4\n", btor2::land("12", "2", "3", "4"));
  ASSERT_EQ("13 and 3 4 5 foo\n", btor2::land("13", "3", "4", "5", "foo"));
}

TEST(btor2, land_variadic)
{
  btor2::nid_t nid = 11;

  // 2 arguments
  ASSERT_EQ("11 and 1 2 3\n", btor2::land(nid, "1", {"2", "3"}));

  ASSERT_EQ(12, nid);

  // 3 arguments
  nid = 11;

  ASSERT_EQ(
    "11 and 1 2 3\n"
    "12 and 1 4 11\n",
    btor2::land(nid, "1", {"2", "3", "4"}));

  ASSERT_EQ(13, nid);

  // 4 arguments
  nid = 11;

  ASSERT_EQ(
    "11 and 1 2 3\n"
    "12 and 1 4 11\n"
    "13 and 1 5 12 foo\n",
    btor2::land(nid, "1", {"2", "3", "4", "5"}, "foo"));

  ASSERT_EQ(14, nid);

  // empty argument
  ASSERT_THROW(btor2::land(nid, "1", {}), std::runtime_error);

  ASSERT_EQ(14, nid);

  // single argument
  ASSERT_THROW(btor2::land(nid, "1", {"2"}), std::runtime_error);

  ASSERT_EQ(14, nid);
}

// nand ========================================================================

TEST(btor2, nand)
{
  ASSERT_EQ("11 nand 1 2 3\n", btor2::nand("11", "1", "2", "3"));
  ASSERT_EQ("12 nand 2 3 4\n", btor2::nand("12", "2", "3", "4"));
  ASSERT_EQ("13 nand 3 4 5 foo\n", btor2::nand("13", "3", "4", "5", "foo"));
}

// nor =========================================================================

TEST(btor2, nor)
{
  ASSERT_EQ("11 nor 1 2 3\n", btor2::nor("11", "1", "2", "3"));
  ASSERT_EQ("12 nor 2 3 4\n", btor2::nor("12", "2", "3", "4"));
  ASSERT_EQ("13 nor 3 4 5 foo\n", btor2::nor("13", "3", "4", "5", "foo"));
}

// lor =========================================================================

TEST(btor2, lor)
{
  ASSERT_EQ("11 or 1 2 3\n", btor2::lor("11", "1", "2", "3"));
  ASSERT_EQ("12 or 2 3 4\n", btor2::lor("12", "2", "3", "4"));
  ASSERT_EQ("13 or 3 4 5 foo\n", btor2::lor("13", "3", "4", "5", "foo"));
}

TEST(btor2, lor_variadic)
{
  btor2::nid_t nid = 11;

  // 2 arguments
  ASSERT_EQ("11 or 1 2 3\n", btor2::lor(nid, "1", {"2", "3"}));

  ASSERT_EQ(12, nid);

  // 3 arguments
  nid = 11;

  ASSERT_EQ(
    "11 or 1 2 3\n"
    "12 or 1 4 11\n",
    btor2::lor(nid, "1", {"2", "3", "4"}));

  ASSERT_EQ(13, nid);

  // 4 arguments
  nid = 11;

  ASSERT_EQ(
    "11 or 1 2 3\n"
    "12 or 1 4 11\n"
    "13 or 1 5 12 foo\n",
    btor2::lor(nid, "1", {"2", "3", "4", "5"}, "foo"));

  ASSERT_EQ(14, nid);

  // empty argument
  ASSERT_THROW(btor2::lor(nid, "1", {}), std::runtime_error);

  ASSERT_EQ(14, nid);

  // single argument
  ASSERT_THROW(btor2::lor(nid, "1", {"2"}), std::runtime_error);

  ASSERT_EQ(14, nid);
}

// xnor ========================================================================

TEST(btor2, xnor)
{
  ASSERT_EQ("11 xnor 1 2 3\n", btor2::xnor("11", "1", "2", "3"));
  ASSERT_EQ("12 xnor 2 3 4\n", btor2::xnor("12", "2", "3", "4"));
  ASSERT_EQ("13 xnor 3 4 5 foo\n", btor2::xnor("13", "3", "4", "5", "foo"));
}

// lxor ========================================================================

TEST(btor2, lxor)
{
  ASSERT_EQ("11 xor 1 2 3\n", btor2::lxor("11", "1", "2", "3"));
  ASSERT_EQ("12 xor 2 3 4\n", btor2::lxor("12", "2", "3", "4"));
  ASSERT_EQ("13 xor 3 4 5 foo\n", btor2::lxor("13", "3", "4", "5", "foo"));
}

// rol =========================================================================

TEST(btor2, rol)
{
  ASSERT_EQ("11 rol 1 2 3\n", btor2::rol("11", "1", "2", "3"));
  ASSERT_EQ("12 rol 2 3 4\n", btor2::rol("12", "2", "3", "4"));
  ASSERT_EQ("13 rol 3 4 5 foo\n", btor2::rol("13", "3", "4", "5", "foo"));
}

// ror =========================================================================

TEST(btor2, ror)
{
  ASSERT_EQ("11 ror 1 2 3\n", btor2::ror("11", "1", "2", "3"));
  ASSERT_EQ("12 ror 2 3 4\n", btor2::ror("12", "2", "3", "4"));
  ASSERT_EQ("13 ror 3 4 5 foo\n", btor2::ror("13", "3", "4", "5", "foo"));
}

// sll =========================================================================

TEST(btor2, sll)
{
  ASSERT_EQ("11 sll 1 2 3\n", btor2::sll("11", "1", "2", "3"));
  ASSERT_EQ("12 sll 2 3 4\n", btor2::sll("12", "2", "3", "4"));
  ASSERT_EQ("13 sll 3 4 5 foo\n", btor2::sll("13", "3", "4", "5", "foo"));
}

// sra =========================================================================

TEST(btor2, sra)
{
  ASSERT_EQ("11 sra 1 2 3\n", btor2::sra("11", "1", "2", "3"));
  ASSERT_EQ("12 sra 2 3 4\n", btor2::sra("12", "2", "3", "4"));
  ASSERT_EQ("13 sra 3 4 5 foo\n", btor2::sra("13", "3", "4", "5", "foo"));
}

// srl =========================================================================

TEST(btor2, srl)
{
  ASSERT_EQ("11 srl 1 2 3\n", btor2::srl("11", "1", "2", "3"));
  ASSERT_EQ("12 srl 2 3 4\n", btor2::srl("12", "2", "3", "4"));
  ASSERT_EQ("13 srl 3 4 5 foo\n", btor2::srl("13", "3", "4", "5", "foo"));
}

// add =========================================================================

TEST(btor2, add)
{
  ASSERT_EQ("11 add 1 2 3\n", btor2::add("11", "1", "2", "3"));
  ASSERT_EQ("12 add 2 3 4\n", btor2::add("12", "2", "3", "4"));
  ASSERT_EQ("13 add 3 4 5 foo\n", btor2::add("13", "3", "4", "5", "foo"));
}

// mul =========================================================================

TEST(btor2, mul)
{
  ASSERT_EQ("11 mul 1 2 3\n", btor2::mul("11", "1", "2", "3"));
  ASSERT_EQ("12 mul 2 3 4\n", btor2::mul("12", "2", "3", "4"));
  ASSERT_EQ("13 mul 3 4 5 foo\n", btor2::mul("13", "3", "4", "5", "foo"));
}

// sdiv ========================================================================

TEST(btor2, sdiv)
{
  ASSERT_EQ("11 sdiv 1 2 3\n", btor2::sdiv("11", "1", "2", "3"));
  ASSERT_EQ("12 sdiv 2 3 4\n", btor2::sdiv("12", "2", "3", "4"));
  ASSERT_EQ("13 sdiv 3 4 5 foo\n", btor2::sdiv("13", "3", "4", "5", "foo"));
}

// udiv ========================================================================

TEST(btor2, udiv)
{
  ASSERT_EQ("11 udiv 1 2 3\n", btor2::udiv("11", "1", "2", "3"));
  ASSERT_EQ("12 udiv 2 3 4\n", btor2::udiv("12", "2", "3", "4"));
  ASSERT_EQ("13 udiv 3 4 5 foo\n", btor2::udiv("13", "3", "4", "5", "foo"));
}

// smod ========================================================================

TEST(btor2, smod)
{
  ASSERT_EQ("11 smod 1 2 3\n", btor2::smod("11", "1", "2", "3"));
  ASSERT_EQ("12 smod 2 3 4\n", btor2::smod("12", "2", "3", "4"));
  ASSERT_EQ("13 smod 3 4 5 foo\n", btor2::smod("13", "3", "4", "5", "foo"));
}

// srem ========================================================================

TEST(btor2, srem)
{
  ASSERT_EQ("11 srem 1 2 3\n", btor2::srem("11", "1", "2", "3"));
  ASSERT_EQ("12 srem 2 3 4\n", btor2::srem("12", "2", "3", "4"));
  ASSERT_EQ("13 srem 3 4 5 foo\n", btor2::srem("13", "3", "4", "5", "foo"));
}

// urem ========================================================================

TEST(btor2, urem)
{
  ASSERT_EQ("11 urem 1 2 3\n", btor2::urem("11", "1", "2", "3"));
  ASSERT_EQ("12 urem 2 3 4\n", btor2::urem("12", "2", "3", "4"));
  ASSERT_EQ("13 urem 3 4 5 foo\n", btor2::urem("13", "3", "4", "5", "foo"));
}

// sub =========================================================================

TEST(btor2, sub)
{
  ASSERT_EQ("11 sub 1 2 3\n", btor2::sub("11", "1", "2", "3"));
  ASSERT_EQ("12 sub 2 3 4\n", btor2::sub("12", "2", "3", "4"));
  ASSERT_EQ("13 sub 3 4 5 foo\n", btor2::sub("13", "3", "4", "5", "foo"));
}

// saddo =======================================================================

TEST(btor2, saddo)
{
  ASSERT_EQ("11 saddo 1 2 3\n", btor2::saddo("11", "1", "2", "3"));
  ASSERT_EQ("12 saddo 2 3 4\n", btor2::saddo("12", "2", "3", "4"));
  ASSERT_EQ("13 saddo 3 4 5 foo\n", btor2::saddo("13", "3", "4", "5", "foo"));
}

// uaddo =======================================================================

TEST(btor2, uaddo)
{
  ASSERT_EQ("11 uaddo 1 2 3\n", btor2::uaddo("11", "1", "2", "3"));
  ASSERT_EQ("12 uaddo 2 3 4\n", btor2::uaddo("12", "2", "3", "4"));
  ASSERT_EQ("13 uaddo 3 4 5 foo\n", btor2::uaddo("13", "3", "4", "5", "foo"));
}

// sdivo =======================================================================

TEST(btor2, sdivo)
{
  ASSERT_EQ("11 sdivo 1 2 3\n", btor2::sdivo("11", "1", "2", "3"));
  ASSERT_EQ("12 sdivo 2 3 4\n", btor2::sdivo("12", "2", "3", "4"));
  ASSERT_EQ("13 sdivo 3 4 5 foo\n", btor2::sdivo("13", "3", "4", "5", "foo"));
}

// udivo =======================================================================

TEST(btor2, udivo)
{
  ASSERT_EQ("11 udivo 1 2 3\n", btor2::udivo("11", "1", "2", "3"));
  ASSERT_EQ("12 udivo 2 3 4\n", btor2::udivo("12", "2", "3", "4"));
  ASSERT_EQ("13 udivo 3 4 5 foo\n", btor2::udivo("13", "3", "4", "5", "foo"));
}

// smulo =======================================================================

TEST(btor2, smulo)
{
  ASSERT_EQ("11 smulo 1 2 3\n", btor2::smulo("11", "1", "2", "3"));
  ASSERT_EQ("12 smulo 2 3 4\n", btor2::smulo("12", "2", "3", "4"));
  ASSERT_EQ("13 smulo 3 4 5 foo\n", btor2::smulo("13", "3", "4", "5", "foo"));
}

// umulo =======================================================================

TEST(btor2, umulo)
{
  ASSERT_EQ("11 umulo 1 2 3\n", btor2::umulo("11", "1", "2", "3"));
  ASSERT_EQ("12 umulo 2 3 4\n", btor2::umulo("12", "2", "3", "4"));
  ASSERT_EQ("13 umulo 3 4 5 foo\n", btor2::umulo("13", "3", "4", "5", "foo"));
}

// ssubo =======================================================================

TEST(btor2, ssubo)
{
  ASSERT_EQ("11 ssubo 1 2 3\n", btor2::ssubo("11", "1", "2", "3"));
  ASSERT_EQ("12 ssubo 2 3 4\n", btor2::ssubo("12", "2", "3", "4"));
  ASSERT_EQ("13 ssubo 3 4 5 foo\n", btor2::ssubo("13", "3", "4", "5", "foo"));
}

// usubo =======================================================================

TEST(btor2, usubo)
{
  ASSERT_EQ("11 usubo 1 2 3\n", btor2::usubo("11", "1", "2", "3"));
  ASSERT_EQ("12 usubo 2 3 4\n", btor2::usubo("12", "2", "3", "4"));
  ASSERT_EQ("13 usubo 3 4 5 foo\n", btor2::usubo("13", "3", "4", "5", "foo"));
}

// concat ======================================================================

TEST(btor2, concat)
{
  ASSERT_EQ("11 concat 1 2 3\n", btor2::concat("11", "1", "2", "3"));
  ASSERT_EQ("12 concat 2 3 4\n", btor2::concat("12", "2", "3", "4"));
  ASSERT_EQ("13 concat 3 4 5 foo\n", btor2::concat("13", "3", "4", "5", "foo"));
}

// read ========================================================================

TEST(btor2, read)
{
  ASSERT_EQ("11 read 1 2 3\n", btor2::read("11", "1", "2", "3"));
  ASSERT_EQ("12 read 2 3 4\n", btor2::read("12", "2", "3", "4"));
  ASSERT_EQ("13 read 3 4 5 foo\n", btor2::read("13", "3", "4", "5", "foo"));
}

// ite =========================================================================

TEST(btor2, ite)
{
  ASSERT_EQ("11 ite 1 2 3 4\n", btor2::ite("11", "1", "2", "3", "4"));
  ASSERT_EQ("12 ite 2 3 4 5\n", btor2::ite("12", "2", "3", "4", "5"));
  ASSERT_EQ(
    "13 ite 3 4 5 6 foo\n",
    btor2::ite("13", "3", "4", "5", "6", "foo"));
}

// write =======================================================================

TEST(btor2, write)
{
  ASSERT_EQ("11 write 1 2 3 4\n", btor2::write("11", "1", "2", "3", "4"));
  ASSERT_EQ("12 write 2 3 4 5\n", btor2::write("12", "2", "3", "4", "5"));
  ASSERT_EQ(
    "13 write 3 4 5 6 foo\n",
    btor2::write("13", "3", "4", "5", "6", "foo"));
}

// card_constraint_naive =======================================================

TEST(btor2, cardinality_exactly_one_naive)
{
  btor2::nid_t nid = 10;

  ASSERT_EQ(
    "10 constraint 2\n",
    btor2::card_constraint_naive(nid, "1", {"2"}));

  ASSERT_EQ(nid, 11);

  ASSERT_EQ(
    "10 xor 1 2 3\n"
    "11 constraint 10\n",
    btor2::card_constraint_naive(nid = 10, "1", {"2", "3"}));

  ASSERT_EQ(nid, 12);

  ASSERT_EQ(
    "10 or 1 2 3\n"
    "11 or 1 4 10\n"
    "12 constraint 11\n"
    "13 nand 1 2 3\n"
    "14 nand 1 2 4\n"
    "15 nand 1 3 4\n"
    "16 and 1 13 14\n"
    "17 and 1 15 16\n"
    "18 constraint 17\n",
    btor2::card_constraint_naive(nid = 10, "1", {"2", "3", "4"}));

  ASSERT_EQ(nid, 19);

  ASSERT_EQ(
    "10 or 1 2 3\n"
    "11 or 1 4 10\n"
    "12 or 1 5 11\n"
    "13 constraint 12\n"
    "14 nand 1 2 3\n"
    "15 nand 1 2 4\n"
    "16 nand 1 2 5\n"
    "17 nand 1 3 4\n"
    "18 nand 1 3 5\n"
    "19 nand 1 4 5\n"
    "20 and 1 14 15\n"
    "21 and 1 16 20\n"
    "22 and 1 17 21\n"
    "23 and 1 18 22\n"
    "24 and 1 19 23\n"
    "25 constraint 24\n",
    btor2::card_constraint_naive(nid = 10, "1", {"2", "3", "4", "5"}));

  ASSERT_EQ(nid, 26);
}

TEST(btor2, cardinality_exactly_one_naive_verify)
{
  BtorMC btormc(1);

  std::string formula =
    btor2::declare_sort("1", "1") +
    btor2::constd("2", "1", "0") +
    btor2::constd("3", "1", "1");

  std::vector<std::string> vars({"4", "5", "6", "7"});

  btor2::nid_t nid = 8;

  for (const auto & v : vars)
    formula += btor2::state(v, "1");

  formula += btor2::card_constraint_naive(nid, "1", vars);

  // not none
  std::vector<std::string> eqs_zero;
  std::string spec = formula;

  for (const auto & v : vars)
    spec +=
      btor2::eq(eqs_zero.emplace_back(std::to_string(nid++)), "1",  "2", v);

  spec += btor2::land(nid, "1", eqs_zero);
  spec += btor2::bad(nid);

  // not more than one
  std::vector<std::string> eqs_one;

  for (const auto & v : vars)
    spec +=
      btor2::eq(eqs_one.emplace_back(std::to_string(nid++)), "1",  "3", v);

  for (size_t i = 0; i < eqs_one.size() - 1; i++)
    for (size_t j = i + 1; j < eqs_one.size(); j++)
      {
        spec += btor2::land(std::to_string(nid++), "1", eqs_one[i], eqs_one[j]);
        spec += btor2::bad(nid);
      }

  ASSERT_FALSE(btormc.sat(spec));
}

// card_constraint_sinz ========================================================

TEST(btor2, cardinality_exactly_one_sinz)
{
  btor2::nid_t nid = 10;

  ASSERT_EQ(
    "10 constraint 2\n",
    btor2::card_constraint_naive(nid, "1", {"2"}));

  ASSERT_EQ(nid, 11);

  ASSERT_EQ(
    "10 xor 1 2 3\n"
    "11 constraint 10\n",
    btor2::card_constraint_naive(nid = 10, "1", {"2", "3"}));

  ASSERT_EQ(nid, 12);

  ASSERT_EQ(
    "10 or 1 2 3\n"
    "11 or 1 4 10\n"
    "12 constraint 11\n"
    "13 input 1 card_aux_0\n"
    "14 input 1 card_aux_1\n"
    "15 not 1 2\n"
    "16 or 1 13 15\n"
    "17 constraint 16\n"
    "18 not 1 4\n"
    "19 not 1 14\n"
    "20 or 1 18 19\n"
    "21 constraint 20\n"
    "22 not 1 3\n"
    "23 or 1 14 22\n"
    "24 constraint 23\n"
    "25 not 1 13\n"
    "26 or 1 14 25\n"
    "27 constraint 26\n"
    "28 or 1 22 25\n"
    "29 constraint 28\n",
    btor2::card_constraint_sinz(nid = 10, "1", {"2", "3", "4"}));

  ASSERT_EQ(nid, 30);

  ASSERT_EQ(
    "10 or 1 1 2\n"
    "11 or 1 3 10\n"
    "12 or 1 4 11\n"
    "13 constraint 12\n"
    "14 input 1 card_aux_0\n"
    "15 input 1 card_aux_1\n"
    "16 input 1 card_aux_2\n"
    "17 not 1 1\n"
    "18 or 1 14 17\n"
    "19 constraint 18\n"
    "20 not 1 4\n"
    "21 not 1 16\n"
    "22 or 1 20 21\n"
    "23 constraint 22\n"
    "24 not 1 2\n"
    "25 or 1 15 24\n"
    "26 constraint 25\n"
    "27 not 1 14\n"
    "28 or 1 15 27\n"
    "29 constraint 28\n"
    "30 or 1 24 27\n"
    "31 constraint 30\n"
    "32 not 1 3\n"
    "33 or 1 16 32\n"
    "34 constraint 33\n"
    "35 not 1 15\n"
    "36 or 1 16 35\n"
    "37 constraint 36\n"
    "38 or 1 32 35\n"
    "39 constraint 38\n",
    btor2::card_constraint_sinz(nid = 10, "1", {"1", "2", "3", "4"}));

  ASSERT_EQ(nid, 40);
}

TEST(btor2, cardinality_exactly_one_sinz_verify)
{
  BtorMC btormc(1);

  std::string formula =
    btor2::declare_sort("1", "1") +
    btor2::constd("2", "1", "0") +
    btor2::constd("3", "1", "1");

  std::vector<std::string> vars({"4", "5", "6", "7"});

  btor2::nid_t nid = 8;

  for (const auto & v : vars)
    formula += btor2::state(v, "1");

  formula += btor2::card_constraint_sinz(nid, "1", vars);

  // not none
  std::vector<std::string> eqs_zero;
  std::string spec = formula;

  for (const auto & v : vars)
    spec +=
      btor2::eq(eqs_zero.emplace_back(std::to_string(nid++)), "1",  "2", v);

  spec += btor2::land(nid, "1", eqs_zero);
  spec += btor2::bad(nid);

  // not more than one
  std::vector<std::string> eqs_one;

  for (const auto & v : vars)
    spec +=
      btor2::eq(eqs_one.emplace_back(std::to_string(nid++)), "1",  "3", v);

  for (size_t i = 0; i < eqs_one.size() - 1; i++)
    for (size_t j = i + 1; j < eqs_one.size(); j++)
      {
        spec += btor2::land(std::to_string(nid++), "1", eqs_one[i], eqs_one[j]);
        spec += btor2::bad(nid);
      }

  ASSERT_FALSE(btormc.sat(spec));
}

} // namespace test
