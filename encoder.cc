#include "encoder.hh"

#include <limits>
#include <iomanip>

#include "smtlib.hh"
#include "program.hh"

/*******************************************************************************
 * global naming definitions
 ******************************************************************************/

/* machine word size - shouldn't change but well ... just in case */
int wordSize = numeric_limits<word>::digits;

/* bitvector definition for the given word size - used frequently */
string bitvecWord = smtlib::bitVector(to_string(wordSize));

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
 * SMT-Lib v2.5 Program Encoder Class
 ******************************************************************************/
smtlib::Encoder::Encoder (Program & p, unsigned long b) : program(p), bound(b)
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
  formula << smtlib::assert(stmtVar(1, 0)) << endl;

  /* encode the program */
  for (step = 1; step <= bound; step++)
    {
      formula << left
              << setw(80)
              << setfill(';')
              << ("; step " + to_string(step) + " ")
              << endl;

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
              word prevPc = *(predecessors[pc].begin());

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

              for (word prevPc : predecessors[pc])
                {
                  old.activator = stmtVar(prevStep, prevPc);
                  old.mem       = memVar(prevStep, prevPc);
                  old.accu      = accuVar(prevStep, prevPc);
                  old.heap      = heapVar(prevStep, prevPc);

                  cur.activator = smtlib::land(curStmt, old.activator);

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
}

/* smtlib::Encoder::collectPredecessors (void) ********************************/
void smtlib::Encoder::collectPredecessors ()
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

/* smtlib::Encoder::addHeader (void) ******************************************/
void smtlib::Encoder::addHeader ()
{
  formula << "; program: " << program.getPath() << endl;
  formula << "; bound: " << bound << endl << endl;

  /* add used logic */
  formula << smtlib::setLogic() << endl;
}

/* smtlib::Encoder::addFooter (void) ******************************************/
void smtlib::Encoder::addFooter ()
{
  formula << smtlib::checkSat() << endl;
  formula << smtlib::exit() << endl;
}

/* smtlib::Encoder::addStmtDeclarations (void) ********************************/
void smtlib::Encoder::addStmtDeclarations ()
{
  word length = program.size();

  formula << "; activation - STMT_<bound>_<pc>" << endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula << smtlib::declareVar(stmtVar(step, pc), "Bool") << endl;

  /* final statement variable */
  formula << smtlib::declareVar(stmtFinal, "Bool") << endl;

  formula << endl;
}

/* smtlib::Encoder::addMemDeclerations (void) *********************************/
void smtlib::Encoder::addMemDeclarations ()
{
  word length = program.size();

  formula << "; mem - MEM_<bound>_<pc>" << endl;

  /* initial accu variable */
  formula << smtlib::declareVar(memInitial, bitvecWord) << endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula << smtlib::declareVar(memVar(step, pc), bitvecWord) << endl;

  /* final mem variable */
  formula << smtlib::declareVar(memFinal, bitvecWord) << endl;

  formula << endl;
}

/* smtlib::Encoder::addAccuDeclarations (void) ********************************/
void smtlib::Encoder::addAccuDeclarations ()
{
  word length = program.size();

  formula << "; accumulator - ACCU_<bound>_<pc>" << endl;

  /* initial accu variable */
  formula << smtlib::declareVar(accuInitial, bitvecWord) << endl;
  formula << smtlib::assert(smtlib::equality(accuInitial, word2Hex(0))) << endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula << smtlib::declareVar(accuVar(step, pc), bitvecWord) << endl;

  /* final accu variable */
  formula << smtlib::declareVar(accuFinal, bitvecWord) << endl;

  formula << endl;
}

/* smtlib::Encoder::addHeapDeclarations (void) ********************************/
void smtlib::Encoder::addHeapDeclarations ()
{
  word length = program.size();

  formula << "; machine memory - HEAP_<bound>_<pc>" << endl;

  /* initial heap variable */
  formula <<  smtlib::declareVar(
                heapInitial,
                smtlib::array(bitvecWord, bitvecWord))
          <<  endl;

  for (step = 1; step <= bound; step++)
    for (pc = 0; pc < length; pc++)
      formula <<  smtlib::declareVar(
                    heapVar(step, pc),
                    smtlib::array(bitvecWord, bitvecWord))
              <<  endl;

  /* final heap variable */
  formula <<  smtlib::declareVar(
                heapFinal,
                smtlib::array(bitvecWord, bitvecWord))
          <<  endl;

  formula << endl;
}

/* smtlib::Encoder::addExitDeclarations (void) ********************************/
void smtlib::Encoder::addExitDeclarations ()
{
  formula << "; exit status" << endl;
  formula << smtlib::declareVar(exitVar, "Bool") << endl;
  formula << smtlib::declareVar(exitCodeVar, bitvecWord) << endl;
  formula << endl;
}

/* smtlib::Encoder::print (void) **********************************************/
void smtlib::Encoder::print ()
{
  cout << formula.str();
}

/* smtlib::Encoder::toString (void) *******************************************/
string smtlib::Encoder::toString ()
{
  return formula.str();
}

/*******************************************************************************
 * encoding functions
 ******************************************************************************/

/* smtlib::Encoder::imply (string, string) ************************************/
inline string smtlib::Encoder::imply (string condition, string expr)
{
  return smtlib::assert(smtlib::implication(condition, expr));
}

/* smtlib::Encoder::load (void) ***********************************************/
inline string smtlib::Encoder::load (Load & l)
{
  if (l.indirect)
    return smtlib::select(cur.heap, smtlib::select(cur.heap, word2Hex(l.arg)));
  else
    return smtlib::select(cur.heap, word2Hex(l.arg));
}

/* smtlib::Encoder::assignVariable (string, string) ***************************/
inline string smtlib::Encoder::assignVariable (string dest, string src)
{
  return imply(cur.activator, smtlib::equality(dest, src));
}

/* smtlib::Encoder::restoreMem (void) *****************************************/
inline void smtlib::Encoder::restoreMem ()
{
  formula << assignVariable(cur.mem, old.mem) << endl;
}

/* smtlib::Encoder::restoreAccu (void) ****************************************/
inline void smtlib::Encoder::restoreAccu ()
{
  formula << assignVariable(cur.accu, old.accu) << endl;
}

/* smtlib::Encoder::restoreHeap (void) ****************************************/
inline void smtlib::Encoder::restoreHeap ()
{
  formula << assignVariable(cur.heap, old.heap) << endl;
}

/* smtlib::Encoder::assignAccu (string) ***************************************/
inline void smtlib::Encoder::assignAccu (string val)
{
  formula << imply(cur.activator, smtlib::equality(cur.accu, val)) << endl;
}

/* smtlib::Encoder::assignHeap (string, string) *******************************/
inline void smtlib::Encoder::assignHeap (string idx, string val)
{
  formula <<  imply(
                cur.activator,
                smtlib::equality(cur.heap, smtlib::store(old.heap, idx, val)))
          <<  endl;
}

/* smtlib::Encoder::assignFinal (void) ****************************************/
inline void smtlib::Encoder::assignFinal ()
{
  string stmt = stmtVar(step, pc);

  formula <<  endl
          <<  imply(stmt, stmtFinal) << endl
          <<  imply(stmt, smtlib::equality(memFinal, cur.mem)) << endl
          <<  imply(stmt, smtlib::equality(accuFinal, cur.accu)) << endl
          <<  imply(stmt, smtlib::equality(heapFinal, cur.heap)) << endl;
}

/* smtlib::Encoder::activate (string, string) *********************************/
inline void smtlib::Encoder::activate (string condition, string target)
{
  if (step < bound)
    formula <<  smtlib::assert(
                  smtlib::implication(
                    condition,
                    target))
            <<  endl;
}

/* smtlib::Encoder::activateNext (void) ***************************************/
inline void smtlib::Encoder::activateNext ()
{
  if (pc < program.size() - 1)
    activate(cur.activator, stmtVar(step + 1, pc + 1));
}

/* smtlib::Encoder::activateJump (string, string) *****************************/
inline void smtlib::Encoder::activateJump (string condition, word target)
{
  activate(smtlib::land(cur.activator, condition), stmtVar(step + 1, target));

  if (pc < program.size() - 1)
    activate(
      smtlib::land(
        cur.activator,
        smtlib::lnot(condition)),
      stmtVar(step + 1, pc + 1));
}

/* LOAD ***********************************************************************/
void smtlib::Encoder::encode (Load & l)
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
void smtlib::Encoder::encode (Store & s)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* assign heap */
  if (s.indirect)
    assignHeap(smtlib::select(old.heap, word2Hex(s.arg)), cur.accu);
  else
    assignHeap(word2Hex(s.arg), cur.accu);

  /* activate next statement */
  activateNext();
}

/* ADD ************************************************************************/
void smtlib::Encoder::encode (Add & a)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smtlib::bvadd(old.accu, load(a)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* ADDI ***********************************************************************/
void smtlib::Encoder::encode (Addi & a)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smtlib::bvadd(old.accu, word2Hex(a.arg)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* SUB ************************************************************************/
void smtlib::Encoder::encode (Sub & s)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smtlib::bvsub(old.accu, load(s)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* SUBI ***********************************************************************/
void smtlib::Encoder::encode (Subi & s)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smtlib::bvsub(old.accu, word2Hex(s.arg)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* CMP ************************************************************************/
void smtlib::Encoder::encode (Cmp & c)
{
  /* restore mem */
  restoreMem();

  /* assign accu */
  assignAccu(smtlib::bvsub(old.accu, load(c)));

  /* restore heap */
  restoreHeap();

  /* activate next statement */
  activateNext();
}

/* JMP ************************************************************************/
void smtlib::Encoder::encode (Jmp & j)
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
void smtlib::Encoder::encode (Jz & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(smtlib::equality(cur.accu, word2Hex(0)), j.arg);
}

/* JNZ ************************************************************************/
void smtlib::Encoder::encode (Jnz & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(smtlib::lnot(smtlib::equality(cur.accu, word2Hex(0))), j.arg);
}

/* JS *************************************************************************/
void smtlib::Encoder::encode (Js & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(
      smtlib::equality(
        "#b1",
        smtlib::extract(
          to_string(wordSize - 1),
          to_string(wordSize - 1),
          cur.accu)),
      j.arg);
}

/* JNS ************************************************************************/
void smtlib::Encoder::encode (Jns & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(
      smtlib::equality(
        "#b0",
        smtlib::extract(
          to_string(wordSize - 1),
          to_string(wordSize - 1),
          cur.accu)),
      j.arg);
}

/* JNZNS **********************************************************************/
void smtlib::Encoder::encode (Jnzns & j)
{
  /* restore mem */
  restoreMem();

  /* restore accu */
  restoreAccu();

  /* restore heap */
  restoreHeap();

  /* activate next statement depending on accu */
  activateJump(
      smtlib::land(
        smtlib::lnot(
          smtlib::equality(
            cur.accu,
            word2Hex(0))),
        smtlib::equality(
          "#b0",
          smtlib::extract(
            to_string(wordSize - 1),
            to_string(wordSize - 1),
            cur.accu))),
      j.arg);
}

/* MEM ************************************************************************/
void smtlib::Encoder::encode (Mem & m)
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
void smtlib::Encoder::encode (Cas & c)
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
void smtlib::Encoder::encode (Sync & s)
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
void smtlib::Encoder::encode (Exit & e)
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
