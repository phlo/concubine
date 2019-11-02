#ifndef SMTLIB_HH_
#define SMTLIB_HH_

#include "common.hh"

#include <cassert>
#include <iomanip>
#include <sstream>
#include <unordered_map>
#include <vector>

namespace ConcuBinE::smtlib {

//==============================================================================
// SMT-Lib v2.5 std::string generators for commonly used expressions
//==============================================================================

// constants
//
const std::string TRUE = "true";
const std::string FALSE = "false";

// convert integer to its word sized SMT-Lib hex constant
//
inline std::string word2hex (const word_t val)
{
  static std::unordered_map<word_t, std::string> values;

  const auto it = values.find(val);

  if (it == values.end())
    {
      std::ostringstream s;
      s << "#x"
        << std::setfill('0')
        << std::setw(word_size / 4)
        << std::hex
        << val;

      return values.emplace(val, s.str()).first->second;
    }

  return it->second;
}

// comment
//
inline std::string comment (const std::string & comment)
{
  return "; " + comment;
}

// comment line
//
const std::string comment_line =
  ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;"
  ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n";

// comment section
//
inline std::string comment_section (const std::string & comment)
{
  std::string c = comment_line + "; ";
  c += comment;
  c += eol;
  c += comment_line;
  c += eol;
  return c;
}

// comment subsection
//
inline std::string comment_subsection (const std::string & comment)
{
  std::string c = comment_line + eol;
  c[1] = ' ';
  c[comment.size() + 2] = ' ';
  return c.replace(2, comment.size(), comment);
}

// expression builders
//
template <class ... T>
inline std::string expr (const char * op, const T & ... args)
{
  std::string e;
  (e += '(') += op;
  (((e += ' ') += args), ...);
  return e += ')';
}

template <template <class, class...> class C>
inline std::string expr (const char * op, const C<std::string> & args)
{
  std::string e;
  (e += '(') += op;
  for (const auto & a : args)
    (e += ' ') += a;
  return e += ')';
}

// definition helpers
//
#define UNARY_OR_MORE(name, op) \
template <template<class, class...> class C> \
inline std::string name (const C<std::string> & args) \
{ \
  const size_t nargs = args.size(); \
  assert(nargs); \
  return nargs < 2 ? *args.begin() : expr(op, args); \
} \
inline std::string name (const std::string & arg) { return arg; } \
template <class ... T> \
inline std::string name (const std::string & arg, const T & ... args) \
{ \
  return expr(op, arg, args...); \
}

#define BINARY_OR_MORE(name, op) \
template <template<class, class...> class C> \
inline std::string name (const C<std::string> & args) \
{ \
  assert(args.size() && args.size() > 1); \
  return expr(op, args); \
} \
template <class ... T> \
inline std::string name (const std::string & arg1, \
                         const std::string & arg2, \
                         const T & ... args) \
{ \
  return expr(op, arg1, arg2, args...); \
}

// assertion
//
inline std::string assertion (const std::string & arg)
{
  return expr("assert", arg);
}

// logical not
//
inline std::string lnot (const std::string & arg)
{
  return expr("not", arg);
}

// logical and
//
UNARY_OR_MORE(land, "and")

// logical or
//
UNARY_OR_MORE(lor, "or")

// logical xor
//
UNARY_OR_MORE(lxor, "xor")

// implication
//
inline std::string implication (const std::string & antecedent,
                                const std::string & consequent)
{
  return expr("=>", antecedent, consequent);
}

// equality
//
BINARY_OR_MORE(equality, "=")

// if-then-else
//
inline std::string ite (const std::string & condition,
                        const std::string & t,
                        const std::string & f)
{
  return expr("ite", condition, t, f);
}

// bit-vector add
//
BINARY_OR_MORE(bvadd, "bvadd")

// bit-vector sub
//
BINARY_OR_MORE(bvsub, "bvsub")

// bit-vector mul
//
BINARY_OR_MORE(bvmul, "bvmul")

// array select
//
inline std::string select (const std::string & array, const std::string & index)
{
  return expr("select", array, index);
}

// array store
//
inline std::string store (const std::string & array,
                          const std::string & index,
                          const std::string & value)
{
  return expr("store", array, index, value);
}

// bit-vector extract
//
inline std::string extract (const std::string & msb,
                            const std::string & lsb,
                            const std::string & bitvec)
{
  return expr(expr("_ extract", msb, lsb).c_str(), bitvec);
}

// bit-vector sort
//
inline std::string bitvector (const unsigned size)
{
  return expr("_ BitVec", std::to_string(size));
}

// array sort
//
inline std::string array (const std::string & idx, const std::string & val)
{
  return expr("Array", idx, val);
}

// variable declaration
//
inline std::string declare_var (const std::string & name,
                                const std::string & sort)
{
  static const std::string pars = "()";
  return expr("declare-fun", name, pars, sort);
}

// boolean variable declaration
//
inline std::string declare_bool_var (const std::string & name)
{
  return declare_var(name, "Bool");
}

// bitvector variable declaration
//
inline std::string declare_bv_var (const std::string & name,
                                   const unsigned size)
{
  return declare_var(name, bitvector(size));
}

// array variable declaration
//
inline std::string declare_array_var (const std::string & name,
                                      const std::string & idx,
                                      const std::string & val)
{
  return declare_var(name, array(idx, val));
}

// set logic to QF_AUFBV
//
inline std::string set_logic () { return "(set-logic QF_AUFBV)"; }

// check satisfiability
//
inline std::string check_sat () { return "(check-sat)"; }

// get model
//
inline std::string get_model () { return "(get-model)"; }

// exit solver
//
inline std::string exit () { return "(exit)"; }

// boolean cardinality constraint =1: naive (pair wise)
//
inline std::string card_constraint_naive (const std::vector<std::string> & vars)
{
  const size_t n = vars.size();

  assert(n);

  switch (n)
    {
    case 1: return assertion(vars.front()) += eol;
    case 2: return assertion(lxor(vars)) += eol;
    default: break;
    }

  // >= 1 constraint
  std::string constraint = assertion(lor(vars)) += eol;

  // <= 1 constraint
  for (auto it1 = vars.begin(); it1 != vars.end(); ++it1)
    for (auto it2 = it1 + 1; it2 != vars.end(); ++it2)
      (constraint += assertion(lor(lnot(*it1), lnot(*it2)))) += eol;

  return constraint;
}

// boolean cardinality constraint =1: Carsten Sinz's sequential counter
//
inline std::string card_constraint_sinz (const std::vector<std::string> & vars)
{
  const size_t n = vars.size();

  assert(n);

  switch (n)
    {
    case 1: return assertion(vars.front()) + eol;
    case 2: return assertion(lxor(vars)) + eol;
    default: break;
    }

  std::string constraint;

  // n-1 auxiliary variables
  std::vector<std::string> auxs;
  auxs.reserve(n - 1);

  const auto end = --vars.end();

  for (auto it = vars.begin(); it != end; ++it)
    {
      constraint += declare_bool_var(auxs.emplace_back(*it + "_aux"));
      constraint += eol;
    }

  // >= 1 constraint
  constraint += eol;
  constraint += assertion(lor(vars));
  constraint += eol;

  // <= 1 constraint
  auto var = vars.begin();
  auto aux = auxs.begin();

  constraint += assertion(lor(lnot(*var), *aux));
  constraint += eol;

  while (++var != end)
    {
      const std::string & aux_prev = *aux++;

      constraint += assertion(lor(lnot(*var), *aux));
      constraint += eol;
      constraint += assertion(lor(lnot(aux_prev), *aux));
      constraint += eol;
      constraint += assertion(lor(lnot(*var), lnot(aux_prev)));
      constraint += eol;
    }

  constraint += assertion(lor(lnot(*var), lnot(*aux)));
  constraint += eol;

  return constraint;
}

} // namespace ConcuBinE::smtlib

#endif
