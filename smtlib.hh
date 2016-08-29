#ifndef SMTLIB_HH_
#define SMTLIB_HH_

#include <string>

/*******************************************************************************
 * SMT-Lib v2.5 std::string generators for commonly used expressions
 *
 * Note: namespace to avoid hiding problems due to frequently occurring names
 ******************************************************************************/
namespace smtlib
{
  inline std::string unaryExpr (std::string op, std::string arg)
    {
      return "(" + op + " " + arg + ")";
    }

  inline std::string binaryExpr (
                                 std::string op,
                                 std::string arg1,
                                 std::string arg2
                                )
    {
      return "(" + op + " " + arg1 + " " + arg2 + ")";
    }

  inline std::string ternaryExpr (
                                  std::string op,
                                  std::string arg1,
                                  std::string arg2,
                                  std::string arg3
                                 )
    {
      return "(" + op + " " + arg1 + " " + arg2 + " " + arg3 + ")";
    }

  /* assertion ****************************************************************/
  inline std::string assert (std::string arg)
    {
      return unaryExpr("assert", arg);
    }

  /* logical not **************************************************************/
  inline std::string lnot (std::string arg)
    {
      return unaryExpr("not", arg);
    }

  /* logical or ***************************************************************/
  inline std::string lor (std::string arg1, std::string arg2)
    {
      return binaryExpr("or", arg1, arg2);
    }

  /* logical and **************************************************************/
  inline std::string land (std::string arg1, std::string arg2)
    {
      return binaryExpr("and", arg1, arg2);
    }

  /* equality *****************************************************************/
  inline std::string equality (std::string arg1, std::string arg2)
    {
      return binaryExpr("=", arg1, arg2);
    }

  /* implication **************************************************************/
  inline std::string implication (std::string arg1, std::string arg2)
    {
      return binaryExpr("=>", arg1, arg2);
    }

  /* bit-vector add ***********************************************************/
  inline std::string bvadd (std::string arg1, std::string arg2)
    {
      return binaryExpr("bvadd", arg1, arg2);
    }

  /* bit-vector sub ***********************************************************/
  inline std::string bvsub (std::string arg1, std::string arg2)
    {
      return binaryExpr("bvsub", arg1, arg2);
    }

  /* array select *************************************************************/
  inline std::string select (std::string array, std::string index)
    {
      return binaryExpr("select", array, index);
    }

  /* array store **************************************************************/
  inline std::string store (
                            std::string arg1,
                            std::string arg2,
                            std::string arg3
                           )
    {
      return ternaryExpr("store", arg1, arg2, arg3);
    }

  /* bit-vector extract *******************************************************/
  inline std::string extract (
                              std::string start,
                              std::string end,
                              std::string bitvec
                             )
    {
      return unaryExpr(binaryExpr("_ extract", start, end), bitvec);
    }

  /* variable declaration *****************************************************/
  inline std::string declareVar (std::string name, std::string type)
    {
      return ternaryExpr("declare-fun", name, "()", type);
    }

  /* bit-vector declaration ***************************************************/
  inline std::string bitVector (std::string size)
    {
      return unaryExpr("_ BitVec", size);
    }

  /* array declaration ********************************************************/
  inline std::string array (std::string arg1, std::string arg2)
    {
      return binaryExpr("Array", arg1, arg2);
    }

  /* set logic to QF_AUFBV ****************************************************/
  inline std::string setLogic ()
    {
      return "(set-logic QF_AUFBV)";
    }

  /* check satisfiability *****************************************************/
  inline std::string checkSat ()
    {
      return "(check-sat)";
    }

  /* get model ****************************************************************/
  inline std::string getModel ()
    {
      return "(get-model)";
    }

  /* exit solver **************************************************************/
  inline std::string exit ()
    {
      return "(exit)";
    }
}

#endif
