#include <gtest/gtest.h>

#include "btor2.hh"
#include "btormc.hh"
#include "streamredirecter.hh"

using namespace std;

// inline string comment (string)
TEST(Btor2Test, comment)
{
  ASSERT_EQ("; foo", btor2::comment("foo"));
}

// inline string comment_section (string)
TEST(Btor2Test, comment_section)
{
  ASSERT_EQ(
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n"
    "; foo\n"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    btor2::comment_section("foo"));
}

// inline string declare_subsection (string, string, string)
TEST(Btor2Test, comment_subsection)
{
  ASSERT_EQ(
    "; foo ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
    ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n",
    btor2::comment_subsection("foo"));
}

// inline string declare_sort (string, string)
TEST(Btor2Test, declare_sort)
{
  ASSERT_EQ("1 sort bitvec 1\n", btor2::declare_sort("1", "1"));
  ASSERT_EQ("2 sort bitvec 16\n", btor2::declare_sort("2", "16"));
  ASSERT_EQ("3 sort bitvec 32\n", btor2::declare_sort("3", "32"));
}

// inline string declare_array (string, string, string)
TEST(Btor2Test, declare_array)
{
  ASSERT_EQ("1 sort array 2 2\n", btor2::declare_array("1", "2", "2"));
  ASSERT_EQ("2 sort array 16 16\n", btor2::declare_array("2", "16", "16"));
  ASSERT_EQ("3 sort array 32 32\n", btor2::declare_array("3", "32", "32"));
}

// inline string constd (string, string, string)
TEST(Btor2Test, constd)
{
  ASSERT_EQ("12 constd 2 2\n", btor2::constd("12", "2", "2"));
  ASSERT_EQ("13 constd 3 3\n", btor2::constd("13", "3", "3"));
  ASSERT_EQ("14 constd 4 4\n", btor2::constd("14", "4", "4"));

  /* zero one */
  ASSERT_EQ("1 zero 1\n", btor2::constd("1", "1", "0"));
  ASSERT_EQ("2 one 1\n", btor2::constd("2", "1", "1"));
}

// inline string input (string, string)
TEST(Btor2Test, input)
{
  ASSERT_EQ("11 input 1\n", btor2::input("11", "1"));
  ASSERT_EQ("12 input 2\n", btor2::input("12", "2"));
  ASSERT_EQ("13 input 3\n", btor2::input("13", "3"));
}

// inline string state (string, string)
TEST(Btor2Test, state)
{
  ASSERT_EQ("11 state 1\n", btor2::state("11", "1"));
  ASSERT_EQ("12 state 2\n", btor2::state("12", "2"));
  ASSERT_EQ("13 state 3\n", btor2::state("13", "3"));
}

// inline string init (string, string, string, string)
TEST(Btor2Test, init)
{
  ASSERT_EQ("11 init 1 2 3\n", btor2::init("11", "1", "2", "3"));
  ASSERT_EQ("12 init 4 5 6\n", btor2::init("12", "4", "5", "6"));
  ASSERT_EQ("13 init 7 8 9\n", btor2::init("13", "7", "8", "9"));
}

// inline string next (string, string, string, string)
TEST(Btor2Test, next)
{
  ASSERT_EQ("11 next 1 2 3\n", btor2::next("11", "1", "2", "3"));
  ASSERT_EQ("12 next 4 5 6\n", btor2::next("12", "4", "5", "6"));
  ASSERT_EQ("13 next 7 8 9\n", btor2::next("13", "7", "8", "9"));
}

// inline string constraint (string, string)
TEST(Btor2Test, constraint)
{
  ASSERT_EQ("11 constraint 1\n", btor2::constraint("11", "1"));
  ASSERT_EQ("12 constraint 2\n", btor2::constraint("12", "2"));
  ASSERT_EQ("13 constraint 3\n", btor2::constraint("13", "3"));
}

// inline string bad (string, string)
TEST(Btor2Test, bad)
{
  ASSERT_EQ("11 bad 1\n", btor2::bad("11", "1"));
  ASSERT_EQ("12 bad 2\n", btor2::bad("12", "2"));
  ASSERT_EQ("13 bad 3\n", btor2::bad("13", "3"));
}

// inline string fair (string, string)
TEST(Btor2Test, fair)
{
  ASSERT_EQ("11 fair 1\n", btor2::fair("11", "1"));
  ASSERT_EQ("12 fair 2\n", btor2::fair("12", "2"));
  ASSERT_EQ("13 fair 3\n", btor2::fair("13", "3"));
}

// inline string output (string, string)
TEST(Btor2Test, output)
{
  ASSERT_EQ("11 output 1\n", btor2::output("11", "1"));
  ASSERT_EQ("12 output 2\n", btor2::output("12", "2"));
  ASSERT_EQ("13 output 3\n", btor2::output("13", "3"));
}

// inline string justice (string, string, vector<string>)
TEST(Btor2Test, justice)
{
  ASSERT_EQ("11 justice 1 1\n", btor2::justice("11", "1", {"1"}));
  ASSERT_EQ("12 justice 2 1 2\n", btor2::justice("12", "2", {"1", "2"}));
  ASSERT_EQ("13 justice 3 1 2 3\n", btor2::justice("13", "3", {"1", "2", "3"}));
}

// inline string sext (string, string, string)
TEST(Btor2Test, sext)
{
  ASSERT_EQ("11 sext 1 2\n", btor2::sext("11", "1", "2"));
  ASSERT_EQ("12 sext 2 3\n", btor2::sext("12", "2", "3"));
  ASSERT_EQ("13 sext 3 4\n", btor2::sext("13", "3", "4"));
}

// inline string uext (string, string, string)
TEST(Btor2Test, uext)
{
  ASSERT_EQ("11 uext 1 2\n", btor2::uext("11", "1", "2"));
  ASSERT_EQ("12 uext 2 3\n", btor2::uext("12", "2", "3"));
  ASSERT_EQ("13 uext 3 4\n", btor2::uext("13", "3", "4"));
}

// inline string slice (string, string, string, string)
TEST(Btor2Test, slice)
{
  ASSERT_EQ("11 slice 1 3 2\n", btor2::slice("11", "1", "3", "2"));
  ASSERT_EQ("12 slice 2 4 3\n", btor2::slice("12", "2", "4", "3"));
  ASSERT_EQ("13 slice 3 5 4\n", btor2::slice("13", "3", "5", "4"));
}

// inline string lnot (string, string, string)
TEST(Btor2Test, lnot)
{
  ASSERT_EQ("11 not 1 2\n", btor2::lnot("11", "1", "2"));
  ASSERT_EQ("12 not 2 3\n", btor2::lnot("12", "2", "3"));
  ASSERT_EQ("13 not 3 4\n", btor2::lnot("13", "3", "4"));
}

// inline string inc (string nid, string sid, string node)
TEST(Btor2Test, inc)
{
  ASSERT_EQ("11 inc 1 2\n", btor2::inc("11", "1", "2"));
  ASSERT_EQ("12 inc 2 3\n", btor2::inc("12", "2", "3"));
  ASSERT_EQ("13 inc 3 4\n", btor2::inc("13", "3", "4"));
}

// inline string dec (string nid, string sid, string node)
TEST(Btor2Test, dec)
{
  ASSERT_EQ("11 dec 1 2\n", btor2::dec("11", "1", "2"));
  ASSERT_EQ("12 dec 2 3\n", btor2::dec("12", "2", "3"));
  ASSERT_EQ("13 dec 3 4\n", btor2::dec("13", "3", "4"));
}

// inline string neg (string nid, string sid, string node)
TEST(Btor2Test, neg)
{
  ASSERT_EQ("11 neg 1 2\n", btor2::neg("11", "1", "2"));
  ASSERT_EQ("12 neg 2 3\n", btor2::neg("12", "2", "3"));
  ASSERT_EQ("13 neg 3 4\n", btor2::neg("13", "3", "4"));
}

// inline string redand (string nid, string sid, string node)
TEST(Btor2Test, redand)
{
  ASSERT_EQ("11 redand 1 2\n", btor2::redand("11", "1", "2"));
  ASSERT_EQ("12 redand 2 3\n", btor2::redand("12", "2", "3"));
  ASSERT_EQ("13 redand 3 4\n", btor2::redand("13", "3", "4"));
}

// inline string redor (string nid, string sid, string node)
TEST(Btor2Test, redor)
{
  ASSERT_EQ("11 redor 1 2\n", btor2::redor("11", "1", "2"));
  ASSERT_EQ("12 redor 2 3\n", btor2::redor("12", "2", "3"));
  ASSERT_EQ("13 redor 3 4\n", btor2::redor("13", "3", "4"));
}

// inline string redxor (string nid, string sid, string node)
TEST(Btor2Test, redxor)
{
  ASSERT_EQ("11 redxor 1 2\n", btor2::redxor("11", "1", "2"));
  ASSERT_EQ("12 redxor 2 3\n", btor2::redxor("12", "2", "3"));
  ASSERT_EQ("13 redxor 3 4\n", btor2::redxor("13", "3", "4"));
}

// inline string iff (string, string, string, string)
TEST(Btor2Test, iff)
{
  ASSERT_EQ("11 iff 1 2 3\n", btor2::iff("11", "1", "2", "3"));
  ASSERT_EQ("12 iff 2 3 4\n", btor2::iff("12", "2", "3", "4"));
  ASSERT_EQ("13 iff 3 4 5\n", btor2::iff("13", "3", "4", "5"));
}

// inline string implies (string, string, string, string)
TEST(Btor2Test, implies)
{
  ASSERT_EQ("11 implies 1 2 3\n", btor2::implies("11", "1", "2", "3"));
  ASSERT_EQ("12 implies 2 3 4\n", btor2::implies("12", "2", "3", "4"));
  ASSERT_EQ("13 implies 3 4 5\n", btor2::implies("13", "3", "4", "5"));
}

// inline string eq (string, string, string, string)
TEST(Btor2Test, eq)
{
  ASSERT_EQ("11 eq 1 2 3\n", btor2::eq("11", "1", "2", "3"));
  ASSERT_EQ("12 eq 2 3 4\n", btor2::eq("12", "2", "3", "4"));
  ASSERT_EQ("13 eq 3 4 5\n", btor2::eq("13", "3", "4", "5"));
}

// inline string neq (string, string, string, string)
TEST(Btor2Test, neq)
{
  ASSERT_EQ("11 neq 1 2 3\n", btor2::neq("11", "1", "2", "3"));
  ASSERT_EQ("12 neq 2 3 4\n", btor2::neq("12", "2", "3", "4"));
  ASSERT_EQ("13 neq 3 4 5\n", btor2::neq("13", "3", "4", "5"));
}

// inline string sgt (string, string, string, string)
TEST(Btor2Test, sgt)
{
  ASSERT_EQ("11 sgt 1 2 3\n", btor2::sgt("11", "1", "2", "3"));
  ASSERT_EQ("12 sgt 2 3 4\n", btor2::sgt("12", "2", "3", "4"));
  ASSERT_EQ("13 sgt 3 4 5\n", btor2::sgt("13", "3", "4", "5"));
}

// inline string ugt (string, string, string, string)
TEST(Btor2Test, ugt)
{
  ASSERT_EQ("11 ugt 1 2 3\n", btor2::ugt("11", "1", "2", "3"));
  ASSERT_EQ("12 ugt 2 3 4\n", btor2::ugt("12", "2", "3", "4"));
  ASSERT_EQ("13 ugt 3 4 5\n", btor2::ugt("13", "3", "4", "5"));
}

// inline string sgte (string, string, string, string)
TEST(Btor2Test, sgte)
{
  ASSERT_EQ("11 sgte 1 2 3\n", btor2::sgte("11", "1", "2", "3"));
  ASSERT_EQ("12 sgte 2 3 4\n", btor2::sgte("12", "2", "3", "4"));
  ASSERT_EQ("13 sgte 3 4 5\n", btor2::sgte("13", "3", "4", "5"));
}

// inline string ugte (string, string, string, string)
TEST(Btor2Test, ugte)
{
  ASSERT_EQ("11 ugte 1 2 3\n", btor2::ugte("11", "1", "2", "3"));
  ASSERT_EQ("12 ugte 2 3 4\n", btor2::ugte("12", "2", "3", "4"));
  ASSERT_EQ("13 ugte 3 4 5\n", btor2::ugte("13", "3", "4", "5"));
}

// inline string slt (string, string, string, string)
TEST(Btor2Test, slt)
{
  ASSERT_EQ("11 slt 1 2 3\n", btor2::slt("11", "1", "2", "3"));
  ASSERT_EQ("12 slt 2 3 4\n", btor2::slt("12", "2", "3", "4"));
  ASSERT_EQ("13 slt 3 4 5\n", btor2::slt("13", "3", "4", "5"));
}

// inline string ult (string, string, string, string)
TEST(Btor2Test, ult)
{
  ASSERT_EQ("11 ult 1 2 3\n", btor2::ult("11", "1", "2", "3"));
  ASSERT_EQ("12 ult 2 3 4\n", btor2::ult("12", "2", "3", "4"));
  ASSERT_EQ("13 ult 3 4 5\n", btor2::ult("13", "3", "4", "5"));
}

// inline string slte (string, string, string, string)
TEST(Btor2Test, slte)
{
  ASSERT_EQ("11 slte 1 2 3\n", btor2::slte("11", "1", "2", "3"));
  ASSERT_EQ("12 slte 2 3 4\n", btor2::slte("12", "2", "3", "4"));
  ASSERT_EQ("13 slte 3 4 5\n", btor2::slte("13", "3", "4", "5"));
}

// inline string ulte (string, string, string, string)
TEST(Btor2Test, ulte)
{
  ASSERT_EQ("11 ulte 1 2 3\n", btor2::ulte("11", "1", "2", "3"));
  ASSERT_EQ("12 ulte 2 3 4\n", btor2::ulte("12", "2", "3", "4"));
  ASSERT_EQ("13 ulte 3 4 5\n", btor2::ulte("13", "3", "4", "5"));
}

// inline string land (string, string, string, string)
TEST(Btor2Test, land)
{
  ASSERT_EQ("11 and 1 2 3\n", btor2::land("11", "1", "2", "3"));
  ASSERT_EQ("12 and 2 3 4\n", btor2::land("12", "2", "3", "4"));
  ASSERT_EQ("13 and 3 4 5\n", btor2::land("13", "3", "4", "5"));
}

// inline string nand (string, string, string, string)
TEST(Btor2Test, nand)
{
  ASSERT_EQ("11 nand 1 2 3\n", btor2::nand("11", "1", "2", "3"));
  ASSERT_EQ("12 nand 2 3 4\n", btor2::nand("12", "2", "3", "4"));
  ASSERT_EQ("13 nand 3 4 5\n", btor2::nand("13", "3", "4", "5"));
}

// inline string nor (string, string, string, string)
TEST(Btor2Test, nor)
{
  ASSERT_EQ("11 nor 1 2 3\n", btor2::nor("11", "1", "2", "3"));
  ASSERT_EQ("12 nor 2 3 4\n", btor2::nor("12", "2", "3", "4"));
  ASSERT_EQ("13 nor 3 4 5\n", btor2::nor("13", "3", "4", "5"));
}

// inline string lor (string, string, string, string)
TEST(Btor2Test, lor)
{
  ASSERT_EQ("11 or 1 2 3\n", btor2::lor("11", "1", "2", "3"));
  ASSERT_EQ("12 or 2 3 4\n", btor2::lor("12", "2", "3", "4"));
  ASSERT_EQ("13 or 3 4 5\n", btor2::lor("13", "3", "4", "5"));
}

// inline string xnor (string, string, string, string)
TEST(Btor2Test, xnor)
{
  ASSERT_EQ("11 xnor 1 2 3\n", btor2::xnor("11", "1", "2", "3"));
  ASSERT_EQ("12 xnor 2 3 4\n", btor2::xnor("12", "2", "3", "4"));
  ASSERT_EQ("13 xnor 3 4 5\n", btor2::xnor("13", "3", "4", "5"));
}

// inline string lxor (string, string, string, string)
TEST(Btor2Test, lxor)
{
  ASSERT_EQ("11 xor 1 2 3\n", btor2::lxor("11", "1", "2", "3"));
  ASSERT_EQ("12 xor 2 3 4\n", btor2::lxor("12", "2", "3", "4"));
  ASSERT_EQ("13 xor 3 4 5\n", btor2::lxor("13", "3", "4", "5"));
}

// inline string rol (string, string, string, string)
TEST(Btor2Test, rol)
{
  ASSERT_EQ("11 rol 1 2 3\n", btor2::rol("11", "1", "2", "3"));
  ASSERT_EQ("12 rol 2 3 4\n", btor2::rol("12", "2", "3", "4"));
  ASSERT_EQ("13 rol 3 4 5\n", btor2::rol("13", "3", "4", "5"));
}

// inline string ror (string, string, string, string)
TEST(Btor2Test, ror)
{
  ASSERT_EQ("11 ror 1 2 3\n", btor2::ror("11", "1", "2", "3"));
  ASSERT_EQ("12 ror 2 3 4\n", btor2::ror("12", "2", "3", "4"));
  ASSERT_EQ("13 ror 3 4 5\n", btor2::ror("13", "3", "4", "5"));
}

// inline string sll (string, string, string, string)
TEST(Btor2Test, sll)
{
  ASSERT_EQ("11 sll 1 2 3\n", btor2::sll("11", "1", "2", "3"));
  ASSERT_EQ("12 sll 2 3 4\n", btor2::sll("12", "2", "3", "4"));
  ASSERT_EQ("13 sll 3 4 5\n", btor2::sll("13", "3", "4", "5"));
}

// inline string sra (string, string, string, string)
TEST(Btor2Test, sra)
{
  ASSERT_EQ("11 sra 1 2 3\n", btor2::sra("11", "1", "2", "3"));
  ASSERT_EQ("12 sra 2 3 4\n", btor2::sra("12", "2", "3", "4"));
  ASSERT_EQ("13 sra 3 4 5\n", btor2::sra("13", "3", "4", "5"));
}

// inline string srl (string, string, string, string)
TEST(Btor2Test, srl)
{
  ASSERT_EQ("11 srl 1 2 3\n", btor2::srl("11", "1", "2", "3"));
  ASSERT_EQ("12 srl 2 3 4\n", btor2::srl("12", "2", "3", "4"));
  ASSERT_EQ("13 srl 3 4 5\n", btor2::srl("13", "3", "4", "5"));
}

// inline string add (string, string, string, string)
TEST(Btor2Test, add)
{
  ASSERT_EQ("11 add 1 2 3\n", btor2::add("11", "1", "2", "3"));
  ASSERT_EQ("12 add 2 3 4\n", btor2::add("12", "2", "3", "4"));
  ASSERT_EQ("13 add 3 4 5\n", btor2::add("13", "3", "4", "5"));
}

// inline string mul (string, string, string, string)
TEST(Btor2Test, mul)
{
  ASSERT_EQ("11 mul 1 2 3\n", btor2::mul("11", "1", "2", "3"));
  ASSERT_EQ("12 mul 2 3 4\n", btor2::mul("12", "2", "3", "4"));
  ASSERT_EQ("13 mul 3 4 5\n", btor2::mul("13", "3", "4", "5"));
}

// inline string sdiv (string, string, string, string)
TEST(Btor2Test, sdiv)
{
  ASSERT_EQ("11 sdiv 1 2 3\n", btor2::sdiv("11", "1", "2", "3"));
  ASSERT_EQ("12 sdiv 2 3 4\n", btor2::sdiv("12", "2", "3", "4"));
  ASSERT_EQ("13 sdiv 3 4 5\n", btor2::sdiv("13", "3", "4", "5"));
}

// inline string udiv (string, string, string, string)
TEST(Btor2Test, udiv)
{
  ASSERT_EQ("11 udiv 1 2 3\n", btor2::udiv("11", "1", "2", "3"));
  ASSERT_EQ("12 udiv 2 3 4\n", btor2::udiv("12", "2", "3", "4"));
  ASSERT_EQ("13 udiv 3 4 5\n", btor2::udiv("13", "3", "4", "5"));
}

// inline string smod (string, string, string, string)
TEST(Btor2Test, smod)
{
  ASSERT_EQ("11 smod 1 2 3\n", btor2::smod("11", "1", "2", "3"));
  ASSERT_EQ("12 smod 2 3 4\n", btor2::smod("12", "2", "3", "4"));
  ASSERT_EQ("13 smod 3 4 5\n", btor2::smod("13", "3", "4", "5"));
}

// inline string srem (string, string, string, string)
TEST(Btor2Test, srem)
{
  ASSERT_EQ("11 srem 1 2 3\n", btor2::srem("11", "1", "2", "3"));
  ASSERT_EQ("12 srem 2 3 4\n", btor2::srem("12", "2", "3", "4"));
  ASSERT_EQ("13 srem 3 4 5\n", btor2::srem("13", "3", "4", "5"));
}

// inline string urem (string, string, string, string)
TEST(Btor2Test, urem)
{
  ASSERT_EQ("11 urem 1 2 3\n", btor2::urem("11", "1", "2", "3"));
  ASSERT_EQ("12 urem 2 3 4\n", btor2::urem("12", "2", "3", "4"));
  ASSERT_EQ("13 urem 3 4 5\n", btor2::urem("13", "3", "4", "5"));
}

// inline string sub (string, string, string, string)
TEST(Btor2Test, sub)
{
  ASSERT_EQ("11 sub 1 2 3\n", btor2::sub("11", "1", "2", "3"));
  ASSERT_EQ("12 sub 2 3 4\n", btor2::sub("12", "2", "3", "4"));
  ASSERT_EQ("13 sub 3 4 5\n", btor2::sub("13", "3", "4", "5"));
}

// inline string saddo (string, string, string, string)
TEST(Btor2Test, saddo)
{
  ASSERT_EQ("11 saddo 1 2 3\n", btor2::saddo("11", "1", "2", "3"));
  ASSERT_EQ("12 saddo 2 3 4\n", btor2::saddo("12", "2", "3", "4"));
  ASSERT_EQ("13 saddo 3 4 5\n", btor2::saddo("13", "3", "4", "5"));
}

// inline string uaddo (string, string, string, string)
TEST(Btor2Test, uaddo)
{
  ASSERT_EQ("11 uaddo 1 2 3\n", btor2::uaddo("11", "1", "2", "3"));
  ASSERT_EQ("12 uaddo 2 3 4\n", btor2::uaddo("12", "2", "3", "4"));
  ASSERT_EQ("13 uaddo 3 4 5\n", btor2::uaddo("13", "3", "4", "5"));
}

// inline string sdivo (string, string, string, string)
TEST(Btor2Test, sdivo)
{
  ASSERT_EQ("11 sdivo 1 2 3\n", btor2::sdivo("11", "1", "2", "3"));
  ASSERT_EQ("12 sdivo 2 3 4\n", btor2::sdivo("12", "2", "3", "4"));
  ASSERT_EQ("13 sdivo 3 4 5\n", btor2::sdivo("13", "3", "4", "5"));
}

// inline string udivo (string, string, string, string)
TEST(Btor2Test, udivo)
{
  ASSERT_EQ("11 udivo 1 2 3\n", btor2::udivo("11", "1", "2", "3"));
  ASSERT_EQ("12 udivo 2 3 4\n", btor2::udivo("12", "2", "3", "4"));
  ASSERT_EQ("13 udivo 3 4 5\n", btor2::udivo("13", "3", "4", "5"));
}

// inline string smulo (string, string, string, string)
TEST(Btor2Test, smulo)
{
  ASSERT_EQ("11 smulo 1 2 3\n", btor2::smulo("11", "1", "2", "3"));
  ASSERT_EQ("12 smulo 2 3 4\n", btor2::smulo("12", "2", "3", "4"));
  ASSERT_EQ("13 smulo 3 4 5\n", btor2::smulo("13", "3", "4", "5"));
}

// inline string umulo (string, string, string, string)
TEST(Btor2Test, umulo)
{
  ASSERT_EQ("11 umulo 1 2 3\n", btor2::umulo("11", "1", "2", "3"));
  ASSERT_EQ("12 umulo 2 3 4\n", btor2::umulo("12", "2", "3", "4"));
  ASSERT_EQ("13 umulo 3 4 5\n", btor2::umulo("13", "3", "4", "5"));
}

// inline string ssubo (string, string, string, string)
TEST(Btor2Test, ssubo)
{
  ASSERT_EQ("11 ssubo 1 2 3\n", btor2::ssubo("11", "1", "2", "3"));
  ASSERT_EQ("12 ssubo 2 3 4\n", btor2::ssubo("12", "2", "3", "4"));
  ASSERT_EQ("13 ssubo 3 4 5\n", btor2::ssubo("13", "3", "4", "5"));
}

// inline string usubo (string, string, string, string)
TEST(Btor2Test, usubo)
{
  ASSERT_EQ("11 usubo 1 2 3\n", btor2::usubo("11", "1", "2", "3"));
  ASSERT_EQ("12 usubo 2 3 4\n", btor2::usubo("12", "2", "3", "4"));
  ASSERT_EQ("13 usubo 3 4 5\n", btor2::usubo("13", "3", "4", "5"));
}

// inline string concat (string, string, string, string)
TEST(Btor2Test, concat)
{
  ASSERT_EQ("11 concat 1 2 3\n", btor2::concat("11", "1", "2", "3"));
  ASSERT_EQ("12 concat 2 3 4\n", btor2::concat("12", "2", "3", "4"));
  ASSERT_EQ("13 concat 3 4 5\n", btor2::concat("13", "3", "4", "5"));
}

// inline string read (string, string, string, string)
TEST(Btor2Test, read)
{
  ASSERT_EQ("11 read 1 2 3\n", btor2::read("11", "1", "2", "3"));
  ASSERT_EQ("12 read 2 3 4\n", btor2::read("12", "2", "3", "4"));
  ASSERT_EQ("13 read 3 4 5\n", btor2::read("13", "3", "4", "5"));
}

// inline string ite (string, string, string, string, string)
TEST(Btor2Test, ite)
{
  ASSERT_EQ("11 ite 1 2 3 4\n", btor2::ite("11", "1", "2", "3", "4"));
  ASSERT_EQ("12 ite 2 3 4 5\n", btor2::ite("12", "2", "3", "4", "5"));
  ASSERT_EQ("13 ite 3 4 5 6\n", btor2::ite("13", "3", "4", "5", "6"));
}

// inline string write (string, string, string, string, string)
TEST(Btor2Test, write)
{
  ASSERT_EQ("11 write 1 2 3 4\n", btor2::write("11", "1", "2", "3", "4"));
  ASSERT_EQ("12 write 2 3 4 5\n", btor2::write("12", "2", "3", "4", "5"));
  ASSERT_EQ("13 write 3 4 5 6\n", btor2::write("13", "3", "4", "5", "6"));
}

// inline string card_constraint_naive (unsigned &, vector<string> const &)
TEST(Btor2Test, cardinality_exactly_one_naive)
{
  unsigned nid = 10;

  ASSERT_EQ(
    "10 or 1 1 2\n"
    "11 constraint 10\n"
    "12 nand 1 1 2\n"
    "13 constraint 12\n",
    btor2::card_constraint_naive(nid, {"1", "2"}));

  ASSERT_EQ(nid, 12);

  nid = 10;

  // TODO: fix <=1 constraint (nands)
  ASSERT_EQ(
    "10 or 1 1 2\n"
    "11 or 1 3 10\n"
    "12 constraint 11\n"
    "13 nand 1 1 2\n"
    "14 nand 1 1 3\n"
    "15 nand 1 2 3\n",
    btor2::card_constraint_naive(nid, {"1", "2", "3"}));

  ASSERT_EQ(nid, 15);

  nid = 10;

  // TODO: fix <=1 constraint (nands)
  ASSERT_EQ(
    "10 or 1 1 2\n"
    "11 or 1 3 10\n"
    "12 or 1 4 11\n"
    "13 nand 1 1 2\n"
    "14 nand 1 1 3\n"
    "15 nand 1 1 4\n"
    "16 nand 1 2 3\n"
    "17 nand 1 2 4\n"
    "18 nand 1 3 4\n",
    btor2::card_constraint_naive(nid, {"1", "2", "3", "4"}));

  ASSERT_EQ(nid, 19);
}

// TODO
TEST(Btor2Test, cardinality_exactly_one_naive_verify)
{
  BtorMC btormc;

  ostringstream ss;
  StreamRedirecter redirecter(cout, ss);

  string formula = btor2::declare_sort("1", "1");

  vector<string> vars({"2", "3", "4"});

  for (const auto & v : vars)
    formula += btor2::state(v, "1");

  unsigned nid = 5;

  formula += btor2::card_constraint_naive(nid, vars);

  cout << formula << eol << eol << eol;

  /* not none */
  string spec = formula;
  string nid_zero = to_string(nid++);
  spec += btor2::constd(nid_zero, "1", "0");

  for (const auto & v : vars)
    spec += btor2::eq(to_string(nid++), "1",  nid_zero, v);

  // spec += btor2::constraint(to_string(nid), to_string(nid - 1));

  // redirecter.start();

  ASSERT_FALSE(btormc.sat(spec));

  // redirecter.stop();

  /* not more than one */
  spec = formula;

  nid = 10;

  for (size_t i = 0; i < vars.size() - 1; i++)
    for (size_t j = i + 1; j < vars.size(); j++)
      spec += btor2::land(to_string(nid++), "1", vars[i], vars[j]);

  cout << spec << eol;

  // redirecter.start();

  ASSERT_FALSE(btormc.sat(spec));

  // redirecter.stop();
}
