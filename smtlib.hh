#ifndef SMTLIB_HH_
#define SMTLIB_HH_

/*******************************************************************************
 * SMT-Lib v2.5 string generators for commonly used expressions
 *
 * Note: namespace to avoid hiding problems due to frequently occurring names
 ******************************************************************************/
namespace smtlib
{
  inline string unaryExpr (string op, string arg)
    {
      return "(" + op + " " + arg + ")";
    }

  inline string binaryExpr (string op, string arg1, string arg2)
    {
      return "(" + op + " " + arg1 + " " + arg2 + ")";
    }

  inline string ternaryExpr (string op, string arg1, string arg2, string arg3)
    {
      return "(" + op + " " + arg1 + " " + arg2 + " " + arg3 + ")";
    }

  /* assertion ****************************************************************/
  inline string assert (string arg)
    {
      return unaryExpr("assert", arg);
    }

  /* logical not **************************************************************/
  inline string lnot (string arg)
    {
      return unaryExpr("not", arg);
    }

  /* logical or ***************************************************************/
  inline string lor (string arg1, string arg2)
    {
      return binaryExpr("or", arg1, arg2);
    }

  /* logical and **************************************************************/
  inline string land (string arg1, string arg2)
    {
      return binaryExpr("and", arg1, arg2);
    }

  /* equality *****************************************************************/
  inline string equality (string arg1, string arg2)
    {
      return binaryExpr("=", arg1, arg2);
    }

  /* implication **************************************************************/
  inline string implication (string arg1, string arg2)
    {
      return binaryExpr("=>", arg1, arg2);
    }

  /* bit-vector add ***********************************************************/
  inline string bvadd (string arg1, string arg2)
    {
      return binaryExpr("bvadd", arg1, arg2);
    }

  /* bit-vector sub ***********************************************************/
  inline string bvsub (string arg1, string arg2)
    {
      return binaryExpr("bvsub", arg1, arg2);
    }

  /* array select *************************************************************/
  inline string select (string array, string index)
    {
      return binaryExpr("select", array, index);
    }

  /* array store **************************************************************/
  inline string store (string arg1, string arg2, string arg3)
    {
      return ternaryExpr("store", arg1, arg2, arg3);
    }

  /* bit-vector extract *******************************************************/
  inline string extract (string start, string end, string bitvec)
    {
      return unaryExpr(binaryExpr("_ extract", start, end), bitvec);
    }

  /* variable declaration *****************************************************/
  inline string declareVar (string name, string type)
    {
      return ternaryExpr("declare-fun", name, "()", type);
    }

  /* bit-vector declaration ***************************************************/
  inline string bitVector (string size)
    {
      return unaryExpr("_ BitVec", size);
    }

  /* array declaration ********************************************************/
  inline string array (string arg1, string arg2)
    {
      return binaryExpr("Array", arg1, arg2);
    }

  /* set logic to QF_AUFBV ****************************************************/
  inline string setLogic ()
    {
      return "(set-logic QF_AUFBV)";
    }

  /* check satisfiability *****************************************************/
  inline string checkSat ()
    {
      return "(check-sat)";
    }

  /* get model ****************************************************************/
  inline string getModel ()
    {
      return "(get-model)";
    }

  /* exit solver **************************************************************/
  inline string exit ()
    {
      return "(exit)";
    }
}

#endif
