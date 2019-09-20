#ifndef SMTLIB_HH_
#define SMTLIB_HH_

#include "common.hh"

#include <string>
#include <iomanip>
#include <sstream>
#include <vector>

namespace ConcuBinE::smtlib {

//==============================================================================
// SMT-Lib v2.5 std::string generators for commonly used expressions
//==============================================================================

// constants
//
static const std::string TRUE = "true";
static const std::string FALSE = "false";

// converts integer to its word sized SMT-Lib hex constant
//
inline std::string word2hex (const word_t val)
{
  std::ostringstream s;
  s << "#x"
    << std::setfill('0')
    << std::setw(word_size / 4)
    << std::hex
    << val;

  return s.str();
}

// unary expression
//
inline std::string expr (const char * op, const std::string & arg)
{
  return '(' + (op + (' ' + arg + ')'));
}

// binary expression
//
inline std::string expr (const char * op,
                         const std::string & arg1,
                         const std::string & arg2)
{
  return '(' + (op + (' ' + arg1 + ' ' + arg2 + ')'));
}

// ternary expression
//
inline std::string expr (const char * op,
                         const std::string & arg1,
                         const std::string & arg2,
                         const std::string & arg3)
{
  return '(' + (op + (' ' + arg1 + ' ' + arg2 + ' ' + arg3 + ')'));
}

// n-ary expression
//
template <template <class, class...> class C>
inline std::string expr (const char * op, const C<std::string> & args)
{
  std::ostringstream sb;
  sb << '(' << op;
  for (const auto & a : args)
    sb << ' ' << a;
  sb << ')';
  return sb.str();
}

// allows mixing const char and strings in init list
//
inline std::string expr (const char * op,
                         std::initializer_list<std::string> args)
{
  return expr<std::initializer_list>(op, args);
}

#define EXPR_SIGNATURE(name) \
template <template<class, class...> class C> \
inline std::string name (const C<std::string> & args) \

#define EXPR_INIIIALIZER_LIST(name) \
inline std::string name (std::initializer_list<std::string> args) \
  { \
    return name<std::initializer_list>(args); \
  }

#define EXPR_UNARY_OR_MORE(name, op) \
EXPR_SIGNATURE(name) \
  { \
    size_t nargs = args.size(); \
    if (!nargs) throw std::runtime_error("no arguments"); \
    return nargs < 2 \
      ? *args.begin() \
      : expr(op, args); \
  } \
EXPR_INIIIALIZER_LIST(name)

#define EXPR_BINARY_OR_MORE(name, op) \
EXPR_SIGNATURE(name) \
  { \
    size_t nargs = args.size(); \
    if (!nargs) throw std::runtime_error("no arguments"); \
    else if (nargs < 2) throw std::runtime_error("single argument"); \
    return expr(op, args); \
  } \
EXPR_INIIIALIZER_LIST(name)

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
  return comment_line + "; " + comment + eol + comment_line + eol;
}

// comment subsection
//
inline std::string comment_subsection (const std::string & comment)
{
  std::string c = comment_line + eol;
  return c.replace(1, 2 + comment.size(), " " + comment + " ");
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
EXPR_UNARY_OR_MORE(land, "and")

// logical or
//
EXPR_UNARY_OR_MORE(lor, "or")

// logical xor
//
EXPR_UNARY_OR_MORE(lxor, "xor")

// implication
//
inline std::string implication (const std::string & antecedent,
                                const std::string & consequent)
{
  return expr("=>", antecedent, consequent);
}

// equality
//
EXPR_BINARY_OR_MORE(equality, "=")

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
EXPR_BINARY_OR_MORE(bvadd, "bvadd")

// bit-vector sub
//
EXPR_BINARY_OR_MORE(bvsub, "bvsub")

// bit-vector mul
//
EXPR_BINARY_OR_MORE(bvmul, "bvmul")

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
inline std::string array (const std::string & idx_t, const std::string & val_t)
{
  return expr("Array", idx_t, val_t);
}

// variable declaration
//
inline std::string declare_var (const std::string & name,
                                const std::string & sort)
{
  return expr("declare-fun", name, "()", sort);
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
                                      const std::string & idx_t,
                                      const std::string & val_t)
{
  return declare_var(name, array(idx_t, val_t));
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
  switch (vars.size())
    {
    case 0: throw std::runtime_error("no arguments");
    case 1: return assertion(vars.front()) + eol;
    case 2: return assertion(lxor(vars)) + eol;
    default: break;
    }

  std::ostringstream constraint;
  std::vector<std::string>::const_iterator it1, it2;

  // require one to be true
  constraint << assertion(lor(vars)) << eol;

  // iterators
  for (it1 = vars.begin(); it1 != vars.end(); ++it1)
    for (it2 = it1 + 1; it2 != vars.end(); ++it2)
      constraint << assertion(lor({lnot(*it1), lnot(*it2)})) << eol;

  // indices
  /*
  for (size_t i = 0; i < vars.size(); i++)
    for (size_t j = i + 1; j < vars.size(); j++)
      constraint << assertion(lor({lnot(vars[i]), lnot(vars[j])})) << eol;
  */

  return constraint.str();
}

// boolean cardinality constraint =1: Carsten Sinz's sequential counter
//
inline std::string card_constraint_sinz (const std::vector<std::string> & vars)
{
  size_t n = vars.size();

  switch (n)
    {
    case 0: throw std::runtime_error("no arguments");
    case 1: return assertion(vars.front()) + eol;
    case 2: return assertion(lxor(vars)) + eol;
    default: break;
    }

  std::vector<std::string> aux;
  std::ostringstream constraint;

  // n-1 auxiliary variables
  for (size_t i = 0; i < n - 1; i++)
    {
      aux.push_back(vars[i] + "_aux");
      constraint << declare_var(aux[i], "Bool") << eol;
    }

  // constraint
  constraint
    << eol
    << assertion(lor(vars))
    << eol
    << assertion(lor({lnot(vars[0]), aux[0]}))
    << eol
    << assertion(lor({lnot(vars[n - 1]), lnot(aux[n - 2])}))
    << eol;

  for (size_t i = 1; i < n - 1; i++)
    constraint
      << assertion(lor({lnot(vars[i]), aux[i]}))
      << eol
      << assertion(lor({lnot(aux[i - 1]), aux[i]}))
      << eol
      << assertion(lor({lnot(vars[i]), lnot(aux[i - 1])}))
      << eol;

  return constraint.str();
}

} // namespace ConcuBinE::smtlib

#endif
