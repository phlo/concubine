#include "smtlib2.hh"

#include <iomanip>

/*******************************************************************************
 * SMT-Lib v2 string generators for commonly used expressions
 *
 * Note: namespace to avoid hiding problems due to frequently occurring names
 ******************************************************************************/
namespace smt
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


/*******************************************************************************
 * global naming definitions
 ******************************************************************************/

/* machine word size - shouldn't change but well ... just in case */
int wordSize = numeric_limits<word>::digits;

/* bitvector definition for the given word size - used frequently */
string bitvecWord = smt::bitVector(to_string(wordSize));

/* state variable prefixes (to simplify changes) */
string stmtPrefix = "STMT_";
string memPrefix  = "MEM_";
string accuPrefix = "ACCU_";
string heapPrefix = "HEAP_";

/* statement activation variable names */
string stmtFinal = stmtPrefix + "FINAL";
string stmtVar (unsigned long step, word pc)
{
  return stmtPrefix + to_string(step) + "_" + to_string(pc);
}

/* memory register variable names */
string memInitial = memPrefix + "0";
string memFinal = memPrefix + "FINAL";
string memVar (unsigned long step, word pc)
{
  return memPrefix + to_string(step) + "_" + to_string(pc);
}

/* accu variable names */
string accuInitial = accuPrefix + "0";
string accuFinal = accuPrefix + "FINAL";
string accuVar (unsigned long step, word pc)
{
  return accuPrefix + to_string(step) + "_" + to_string(pc);
}

/* machine memory variable names */
string heapInitial = heapPrefix + "0";
string heapFinal = heapPrefix + "FINAL";
string heapVar (unsigned long step, word pc)
{
  return heapPrefix + to_string(step) + "_" + to_string(pc);
}

/* exit variable names */
string exitVar = "EXIT";
string exitCodeVar = "EXIT_CODE";

/* converts integer to its word sized smt hex constant*/
string word2Hex (word val)
{
  ostringstream s;

  s << "#x"
    << setfill('0')
    << setw(wordSize / 4)
    << hex
    << val;

  return s.str();
}


/*******************************************************************************
 * SMTLib2 Program Encoder Class
 ******************************************************************************/
SMTLib2::SMTLib2 (Program & p, unsigned long b) : program(p), bound(b)
{
  /* find jump targets */
  collectPredecessors();

  /* add file header */
  addHeader();

  /* add variable declarations */
  addStmtDeclarations();
  addMemDeclarations();
  addAccuDeclarations();
  addHeapDeclarations();
  addExitDeclarations();

  /* add initial activation */
  formula << "; initial activation" << endl;
  formula << smt::assert(stmtVar(1, 0)) << endl;

  /* encode the program */
  for (step = 1; step <= bound; step++)
    {
      formula << left
              << setw(80)
              << setfill(';')
              << ("; step " + to_string(step) + " ")
              << endl;

      word          prevPc    = pc - 1;
      unsigned long prevStep  = step - 1;
      const bool    isFinal   =
                      step == bound ||
                      pc == program.size() - 1 ||
                      dynamic_pointer_cast<Exit>(program[pc]);

      for (pc = 0; pc < program.size(); pc++)
        {
          formula << "; " << program[pc]->getSymbol() << endl;

          /* assign current program state variables */
          cur.activator = stmtVar(step, pc);
          cur.mem       = memVar(step, pc);
          cur.accu      = accuVar(step, pc);
          cur.heap      = heapVar(step, pc);

          /* no predecessor for the very first program statement */
          if (step == 1 || predecessors[pc].empty())
            {
              /* dummy predecessors for first program statement */
              old.mem   = memInitial;
              old.accu  = accuInitial;
              old.heap  = heapInitial;

              program[pc]->encode(*this);
            }
          /* statement is no target of a jump */
          else if (predecessors[pc].size() == 1)
            {
              old.mem   = memVar(prevStep, prevPc);
              old.accu  = accuVar(prevStep, prevPc);
              old.heap  = heapVar(prevStep, prevPc);

              program[pc]->encode(*this);
            }
          /* else generate assertions for all predecessors */
          else
            {
              bool addNewLine = false;

              string curStmt = cur.activator;

              for (word oldPc : predecessors[pc])
                {
                  old.activator = stmtVar(prevStep, oldPc);
                  old.mem       = memVar(prevStep, oldPc);
                  old.accu      = accuVar(prevStep, oldPc);
                  old.heap      = heapVar(prevStep, oldPc);

                  cur.activator = smt::land(curStmt, old.activator);

                  if (addNewLine)
                    formula << endl;
                  else
                    addNewLine = true;

                  program[pc]->encode(*this);
                }
            }

          /* no more statements or bound reached? assign final variables */
          if (isFinal)
            assignFinal();

          formula << endl;
        }
    }

  /* add file footer */
  addFooter();
};

/* SMTLib2::collectPredecessors (void) ****************************************/
void SMTLib2::collectPredecessors ()
{
  word length = program.size();

  for (pc = 0; pc < length; pc++)
    {
      /* add previous statement if pc > 0 */
      if (pc > 0)
        predecessors[pc].insert(pc - 1);

      /* add current pc to predecessors of target statement */
      /* NOTE: possible improvement: remove pc of JMP from successor before
       * adding to the target statement */
      if (JmpPtr j = dynamic_pointer_cast<Jmp>(program[pc]))
        predecessors[j->arg].insert(pc);
    }
}

/* SMTLib2::addHeader (void) **************************************************/
void SMTLib2::addHeader ()
{
  formula << "; program: " << program.getPath() << endl;
  formula << "; bound: " << bound << endl << endl;

  /* add used logic */
  formula << smt::setLogic() << endl;
}

/* SMTLib2::addFooter (void) **************************************************/
void SMTLib2::addFooter ()
{
  formula << smt::checkSat() << endl;
  formula << smt::exit() << endl;
}

/* SMTLib2::addStmtDeclarations (void) ****************************************/
void SMTLib2::addStmtDeclarations ()
{
  word length = program.size();

  formula << "; activation - STMT_<bound>_<pc>" << endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula << smt::declareVar(stmtVar(step, pc), "Bool") << endl;

  /* final statement variable */
  formula << smt::declareVar(stmtFinal, "Bool") << endl;

  formula << endl;
}

/* SMTLib2::addMemDeclerations (void) *****************************************/
void SMTLib2::addMemDeclarations ()
{
  word length = program.size();

  formula << "; mem - MEM_<bound>_<pc>" << endl;

  /* initial accu variable */
  formula << smt::declareVar(memInitial, bitvecWord) << endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula << smt::declareVar(memVar(step, pc), bitvecWord) << endl;

  /* final mem variable */
  formula << smt::declareVar(memFinal, bitvecWord) << endl;

  formula << endl;
}

/* SMTLib2::addAccuDeclarations (void) ****************************************/
void SMTLib2::addAccuDeclarations ()
{
  word length = program.size();

  formula << "; accumulator - ACCU_<bound>_<pc>" << endl;

  /* initial accu variable */
  formula << smt::declareVar(accuInitial, bitvecWord) << endl;
  formula << smt::assert(smt::equality(accuInitial, word2Hex(0))) << endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula << smt::declareVar(accuVar(step, pc), bitvecWord) << endl;

  /* final accu variable */
  formula << smt::declareVar(accuFinal, bitvecWord) << endl;

  formula << endl;
}

/* SMTLib2::addHeapDeclarations (void) ****************************************/
void SMTLib2::addHeapDeclarations ()
{
  word length = program.size();

  formula << "; machine memory - HEAP_<bound>_<pc>" << endl;

  /* initial heap variable */
  formula <<  smt::declareVar(heapInitial, smt::array(bitvecWord, bitvecWord))
          <<  endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula <<  smt::declareVar(
                    heapVar(step, pc),
                    smt::array(bitvecWord, bitvecWord))
              <<  endl;

  /* final heap variable */
  formula <<  smt::declareVar(
                heapFinal,
                smt::array(bitvecWord, bitvecWord))
          <<  endl;

  formula << endl;
}

/* SMTLib2::addExitDeclarations (void) ****************************************/
void SMTLib2::addExitDeclarations ()
{
  formula << "; exit status" << endl;
  formula << smt::declareVar(exitVar, "Bool") << endl;
  formula << smt::declareVar(exitCodeVar, bitvecWord) << endl;
  formula << endl;
}

/* SMTLib2::print (void) ******************************************************/
void SMTLib2::print ()
{
  cout << formula.str();
}

/*******************************************************************************
 * encoding functions
 ******************************************************************************/

/* SMTLib2::imply (string, string) ********************************************/
inline string SMTLib2::imply (string condition, string expr)
{
  return smt::assert(smt::implication(condition, expr));
}

/* SMTLib2::load (void) *******************************************************/
inline string SMTLib2::load (Load & l)
{
  if (l.indirect)
    return smt::select(cur.heap, smt::select(cur.heap, word2Hex(l.arg)));
  else
    return smt::select(cur.heap, word2Hex(l.arg));
}

/* SMTLib2::assignVariable (string, string) ***********************************/
inline string SMTLib2::assignVariable (string dest, string src)
{
  return imply(cur.activator, smt::equality(dest, src));
}

/* SMTLib2::restoreMem (void) *************************************************/
inline void SMTLib2::restoreMem ()
{
  formula << assignVariable(cur.mem, old.mem) << endl;
}

/* SMTLib2::restoreAccu (void) ************************************************/
inline void SMTLib2::restoreAccu ()
{
  formula << assignVariable(cur.accu, old.accu) << endl;
}

/* SMTLib2::restoreHeap (void) ************************************************/
inline void SMTLib2::restoreHeap ()
{
  formula << assignVariable(cur.heap, old.heap) << endl;
}

/* SMTLib2::assignAccu (string) ***********************************************/
inline void SMTLib2::assignAccu (string val)
{
  formula << imply(cur.activator, smt::equality(cur.accu, val)) << endl;
}

/* SMTLib2::assignHeap (string, string) ***************************************/
inline void SMTLib2::assignHeap (string idx, string val)
{
  formula <<  imply(
                cur.activator,
                smt::equality(cur.heap, smt::store(old.heap, idx, val)))
          <<  endl;
}

/* SMTLib2::assignFinal (void) ************************************************/
inline void SMTLib2::assignFinal ()
{
  string stmt = stmtVar(step, pc);

  formula <<  endl
          <<  imply(stmt, stmtFinal) << endl
          <<  imply(stmt, smt::equality(memFinal, cur.mem)) << endl
          <<  imply(stmt, smt::equality(accuFinal, cur.accu)) << endl
          <<  imply(stmt, smt::equality(heapFinal, cur.heap)) << endl;
}

/* SMTLib2::activate (string, string) *****************************************/
inline void SMTLib2::activate (string condition, string target)
{
  if (step < bound)
    formula <<  smt::assert(
                  smt::implication(
                    condition,
                    target))
            <<  endl;
}

/* SMTLib2::activateNext (void) ***********************************************/
inline void SMTLib2::activateNext ()
{
  if (pc < program.size() - 1)
    activate(cur.activator, stmtVar(step + 1, pc + 1));
}

/* SMTLib2::activateJump (string, string) *************************************/
inline void SMTLib2::activateJump (string condition, word target)
{
  activate(smt::land(cur.activator, condition), stmtVar(step + 1, target));

  if (pc < program.size() - 1)
    activate(
      smt::land(
        cur.activator,
        smt::lnot(condition)),
      stmtVar(step + 1, pc + 1));
}

/* LOAD ***********************************************************************/
void SMTLib2::encode (Load & l)
{
  /* restore mem */
  restoreMem();

  /* restore heap */
  restoreHeap();

  /* assign accu */
  assignAccu(load(l));

  /* activate next statement */
  activateNext();
}

/* STORE **********************************************************************/
void SMTLib2::encode (Store & s)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* assign heap */
  if (s.indirect)
    assignHeap(smt::select(old.heap, word2Hex(s.arg)), cur.accu);
  else
    assignHeap(word2Hex(s.arg), cur.accu);

  /* activate next statement */
  activateNext();
}

/* ADD ************************************************************************/
void SMTLib2::encode (Add & a)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smt::bvadd(old.accu, load(a)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* ADDI ***********************************************************************/
void SMTLib2::encode (Addi & a)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smt::bvadd(old.accu, word2Hex(a.arg)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* SUB ************************************************************************/
void SMTLib2::encode (Sub & s)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smt::bvsub(old.accu, load(s)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* SUBI ***********************************************************************/
void SMTLib2::encode (Subi & s)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smt::bvsub(old.accu, word2Hex(s.arg)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* CMP ************************************************************************/
void SMTLib2::encode (Cmp & c)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smt::bvsub(old.accu, load(c)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* JMP ************************************************************************/
void SMTLib2::encode (Jmp & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activate(cur.activator, stmtVar(step + 1, j.arg));
}

/* JZ *************************************************************************/
void SMTLib2::encode (Jz & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(smt::equality(cur.accu, word2Hex(0)), j.arg);
}

/* JNZ ************************************************************************/
void SMTLib2::encode (Jnz & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(smt::lnot(smt::equality(cur.accu, word2Hex(0))), j.arg);
}

/* JS *************************************************************************/
void SMTLib2::encode (Js & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(
      smt::equality(
        "#b1",
        smt::extract(
          to_string(wordSize - 1),
          to_string(wordSize - 1),
          cur.accu)),
      j.arg);
}

/* JNS ************************************************************************/
void SMTLib2::encode (Jns & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(
      smt::equality(
        "#b0",
        smt::extract(
          to_string(wordSize - 1),
          to_string(wordSize - 1),
          cur.accu)),
      j.arg);
}

/* JNZNS **********************************************************************/
void SMTLib2::encode (Jnzns & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(
      smt::land(
        smt::lnot(
          smt::equality(
            cur.accu,
            word2Hex(0))),
        smt::equality(
          "#b0",
          smt::extract(
            to_string(wordSize - 1),
            to_string(wordSize - 1),
            cur.accu))),
      j.arg);
}

/* MEM ************************************************************************/
void SMTLib2::encode (Mem & m)
{
  /* assign mem */
  formula << assignVariable(cur.mem, load(m)) << endl;

  /* assign accu */
  assignAccu(cur.mem);

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* CAS ************************************************************************/
void SMTLib2::encode (Cas & c)
{
  formula <<  "; " << c.getSymbol()
          <<  " not implemented in sequential version!"
          <<  endl;

  restoreMem();
  restoreAccu();
  restoreHeap();

  activateNext();
}

/* SYNC ***********************************************************************/
void SMTLib2::encode (Sync & s)
{
  formula <<  "; " << s.getSymbol()
          <<  " not implemented in sequential version!"
          <<  endl;

  restoreMem();
  restoreAccu();
  restoreHeap();

  activateNext();
}

/* EXIT ***********************************************************************/
void SMTLib2::encode (Exit & e)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* assign exit */
  formula << imply(cur.activator, exitVar) << endl;
  formula << assignVariable(exitCodeVar, word2Hex(e.arg)) << endl;
}
