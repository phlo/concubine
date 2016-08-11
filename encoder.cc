#include "encoder.hh"

#include <limits>
#include <iomanip>

#include "smtlib.hh"
#include "program.hh"

using namespace smtlib;

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
Encoder::Encoder (Program & p, unsigned long b) : program(p), bound(b)
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

/* Encoder::collectPredecessors (void) ****************************************/
void Encoder::collectPredecessors ()
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

/* Encoder::addHeader (void) **************************************************/
void Encoder::addHeader ()
{
  formula << "; program: " << program.getPath() << endl;
  formula << "; bound: " << bound << endl << endl;

  /* add used logic */
  formula << smtlib::setLogic() << endl;
}

/* Encoder::addFooter (void) **************************************************/
void Encoder::addFooter ()
{
  formula << smtlib::checkSat() << endl;
  formula << smtlib::exit() << endl;
}

/* Encoder::addStmtDeclarations (void) ****************************************/
void Encoder::addStmtDeclarations ()
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

/* Encoder::addMemDeclerations (void) *****************************************/
void Encoder::addMemDeclarations ()
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

/* Encoder::addAccuDeclarations (void) ****************************************/
void Encoder::addAccuDeclarations ()
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

/* Encoder::addHeapDeclarations (void) ****************************************/
void Encoder::addHeapDeclarations ()
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

/* Encoder::addExitDeclarations (void) ****************************************/
void Encoder::addExitDeclarations ()
{
  formula << "; exit status" << endl;
  formula << smtlib::declareVar(exitVar, "Bool") << endl;
  formula << smtlib::declareVar(exitCodeVar, bitvecWord) << endl;
  formula << endl;
}

/* Encoder::print (void) ******************************************************/
void Encoder::print ()
{
  cout << formula.str();
}

/* Encoder::toString (void) ***************************************************/
string Encoder::toString ()
{
  return formula.str();
}

/*******************************************************************************
 * encoding functions
 ******************************************************************************/

/* Encoder::imply (string, string) ********************************************/
inline string Encoder::imply (string condition, string expr)
{
  return smtlib::assert(smtlib::implication(condition, expr));
}

/* Encoder::load (void) *******************************************************/
inline string Encoder::load (Load & l)
{
  if (l.indirect)
    return smtlib::select(cur.heap, smtlib::select(cur.heap, word2Hex(l.arg)));
  else
    return smtlib::select(cur.heap, word2Hex(l.arg));
}

/* Encoder::assignVariable (string, string) ***********************************/
inline string Encoder::assignVariable (string dest, string src)
{
  return imply(cur.activator, smtlib::equality(dest, src));
}

/* Encoder::restoreMem (void) *************************************************/
inline void Encoder::restoreMem ()
{
  formula << assignVariable(cur.mem, old.mem) << endl;
}

/* Encoder::restoreAccu (void) ************************************************/
inline void Encoder::restoreAccu ()
{
  formula << assignVariable(cur.accu, old.accu) << endl;
}

/* Encoder::restoreHeap (void) ************************************************/
inline void Encoder::restoreHeap ()
{
  formula << assignVariable(cur.heap, old.heap) << endl;
}

/* Encoder::assignAccu (string) ***********************************************/
inline void Encoder::assignAccu (string val)
{
  formula << imply(cur.activator, smtlib::equality(cur.accu, val)) << endl;
}

/* Encoder::assignHeap (string, string) ***************************************/
inline void Encoder::assignHeap (string idx, string val)
{
  formula <<  imply(
                cur.activator,
                smtlib::equality(cur.heap, smtlib::store(old.heap, idx, val)))
          <<  endl;
}

/* Encoder::assignFinal (void) ************************************************/
inline void Encoder::assignFinal ()
{
  string stmt = stmtVar(step, pc);

  formula <<  endl
          <<  imply(stmt, stmtFinal) << endl
          <<  imply(stmt, smtlib::equality(memFinal, cur.mem)) << endl
          <<  imply(stmt, smtlib::equality(accuFinal, cur.accu)) << endl
          <<  imply(stmt, smtlib::equality(heapFinal, cur.heap)) << endl;
}

/* Encoder::activate (string, string) *****************************************/
inline void Encoder::activate (string condition, string target)
{
  if (step < bound)
    formula <<  smtlib::assert(
                  smtlib::implication(
                    condition,
                    target))
            <<  endl;
}

/* Encoder::activateNext (void) ***********************************************/
inline void Encoder::activateNext ()
{
  if (pc < program.size() - 1)
    activate(cur.activator, stmtVar(step + 1, pc + 1));
}

/* Encoder::activateJump (string, string) *************************************/
inline void Encoder::activateJump (string condition, word target)
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
void Encoder::encode (Load & l)
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
void Encoder::encode (Store & s)
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
void Encoder::encode (Add & a)
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
void Encoder::encode (Addi & a)
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
void Encoder::encode (Sub & s)
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
void Encoder::encode (Subi & s)
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
void Encoder::encode (Cmp & c)
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
void Encoder::encode (Jmp & j)
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
void Encoder::encode (Jz & j)
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
void Encoder::encode (Jnz & j)
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
void Encoder::encode (Js & j)
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
void Encoder::encode (Jns & j)
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
void Encoder::encode (Jnzns & j)
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
void Encoder::encode (Mem & m)
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
void Encoder::encode (Cas & c)
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
void Encoder::encode (Sync & s)
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
void Encoder::encode (Exit & e)
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
