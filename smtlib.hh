#ifndef SMTLIB_HH_
#define SMTLIB_HH_

#include "common.hh"

#include <string>
#include <iomanip>
#include <sstream>
#include <vector>

/*******************************************************************************
 * SMT-Lib v2.5 std::string generators for commonly used expressions
 *
 * Note: namespace to avoid hiding problems due to frequently occurring names
 ******************************************************************************/
namespace smtlib
{
  /* line feed */
  const char endl = '\n';

  /* converts integer to its word sized SMT-Lib hex constant ******************/
  inline std::string word2hex (word val)
    {
      std::ostringstream s;
      s << "#x"
        << std::setfill('0')
        << std::setw(word_size / 4)
        << std::hex
        << val;
      return s.str();
    }

  /* n-ary expression *********************************************************/
  inline std::string expr (
                           const char * op,
                           std::vector<std::string> const & args
                          )
    {
      std::ostringstream sb;
      sb << '(' << op;
      for (const auto & a : args)
        sb << ' ' << a;
      sb << ')';
      return sb.str();
    }

  /* assertion ****************************************************************/
  inline std::string assertion (std::string arg)
    {
      return expr("assert", {arg});
    }

  /* logical not **************************************************************/
  inline std::string lnot (std::string arg)
    {
      return expr("not", {arg});
    }

  /* logical or ***************************************************************/
  inline std::string lor (std::vector<std::string> const & args)
    {
      return expr("or", args);
    }

  /* logical and **************************************************************/
  inline std::string land (std::vector<std::string> const & args)
    {
      return expr("and", args);
    }

  /* implication **************************************************************/
  inline std::string implication (std::string arg1, std::string arg2)
    {
      return expr("=>", {arg1, arg2});
    }

  /* equality *****************************************************************/
  inline std::string equality (std::vector<std::string> const & args)
    {
      return expr("=", args);
    }

  /* bit-vector add ***********************************************************/
  inline std::string bvadd (std::vector<std::string> const & args)
    {
      return expr("bvadd", args);
    }

  /* bit-vector sub ***********************************************************/
  inline std::string bvsub (std::vector<std::string> const & args)
    {
      return expr("bvsub", args);
    }

  /* array select *************************************************************/
  inline std::string select (std::string array, std::string index)
    {
      return expr("select", {array, index});
    }

  /* array store **************************************************************/
  inline std::string store (
                            std::string array,
                            std::string index,
                            std::string value
                           )
    {
      return expr("store", {array, index, value});
    }

  /* bit-vector extract *******************************************************/
  inline std::string extract (
                              std::string msb,
                              std::string lsb,
                              std::string bitvec
                             )
    {
      return expr(expr("_ extract", {msb, lsb}).c_str(), {bitvec});
    }

  /* variable declaration *****************************************************/
  inline std::string declare_var (std::string name, std::string type)
    {
      return expr("declare-fun", {name, "()", type});
    }

  /* bit-vector declaration ***************************************************/
  inline std::string bitvector (std::string size)
    {
      return expr("_ BitVec", {size});
    }

  /* array declaration ********************************************************/
  inline std::string array (std::string arg1, std::string arg2)
    {
      return expr("Array", {arg1, arg2});
    }

  /* set logic to QF_AUFBV ****************************************************/
  inline std::string set_logic ()
    {
      return "(set-logic QF_AUFBV)";
    }

  /* check satisfiability *****************************************************/
  inline std::string check_sat ()
    {
      return "(check-sat)";
    }

  /* get model ****************************************************************/
  inline std::string get_model ()
    {
      return "(get-model)";
    }

  /* exit solver **************************************************************/
  inline std::string exit ()
    {
      return "(exit)";
    }

  /* boolean cardinality constraint =1: naive (pair wise) *********************/
  inline std::string
  card_constraint_naive (std::vector<std::string> const & vars)
    {
      std::ostringstream constraint;
      std::vector<std::string>::const_iterator it1, it2;

      /* require one to be true */
      constraint << assertion(lor(vars)) << endl;

      /* iterators */
      for (it1 = vars.begin(); it1 != vars.end(); ++it1)
        for (it2 = it1 + 1; it2 != vars.end(); ++it2)
          constraint << assertion(lor({lnot(*it1), lnot(*it2)})) << endl;

      /* indices */
      /*
      for (size_t i = 0; i < vars.size(); i++)
        for (size_t j = i + 1; j < vars.size(); j++)
          constraint << assertion(lor({lnot(vars[i]), lnot(vars[j])})) << endl;
      */

      return constraint.str();
    }

  /* boolean cardinality constraint =1: Carsten Sinz's sequential counter *****/
  inline std::string
  card_constraint_sinz (std::vector<std::string> const & vars)
    {
      unsigned int i;
      size_t n = vars.size();
      std::vector<std::string> aux;
      std::ostringstream constraint;

      /* n-1 auxiliary variables */
      for (i = 0; i < n - 1; i++)
        {
          aux.push_back(vars[i] + "_aux");
          constraint << declare_var(aux[i], "Bool") << endl;
        }

      /* constraint */
      constraint
        << endl
        << assertion(lor(vars))
        << endl
        << assertion(lor({lnot(vars[0]), aux[0]}))
        << endl
        << assertion(lor({lnot(vars[n - 1]), lnot(aux[n - 2])}))
        << endl;

      for (i = 1; i < n - 1; i++)
        constraint
          << assertion(lor({lnot(vars[i]), aux[i]}))
          << endl
          << assertion(lor({lnot(aux[i - 1]), aux[i]}))
          << endl
          << assertion(lor({lnot(vars[i]), lnot(aux[i - 1])}))
          << endl;

      return constraint.str();
    }
}
#endif
