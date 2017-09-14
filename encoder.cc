#include "encoder.hh"

#include <iomanip>
#include <iostream>

#include "smtlib.hh"

using namespace std;

/*******************************************************************************
 * global naming definitions
 ******************************************************************************/

/* bitvector definition for the given word size - used frequently */
string bitvecWord = smtlib::bitVector(to_string(word_size));

/* state variable prefixes (to simplify changes) */
string threadPrefix = "THREAD_";
string stmtPrefix   = "STMT_";
string memPrefix    = "MEM_";
string accuPrefix   = "ACCU_";
string heapPrefix   = "HEAP_";

/* thread activation variable names */
string        threadFinal = threadPrefix + "FINAL";
inline string threadVar (unsigned long step, word thread)
{
  return threadPrefix + to_string(step) + '_' + to_string(thread);
}

/* statement activation variable names */
inline string stmtFinal (word thread)
{
  return stmtPrefix + to_string(thread) + "_FINAL";
}
inline string stmtVar (unsigned long step, word thread, word pc)
{
  return stmtPrefix + to_string(step) + '_'
                    + to_string(thread) + '_'
                    + to_string(pc);
}

/* memory register variable names */
string        memInitial = memPrefix + "0";
inline string memFinal (word thread)
{
  return memPrefix + to_string(thread) + "_FINAL";
}
inline string memVar (unsigned long step, word thread)
{
  return memPrefix + to_string(step) + '_' + to_string(thread);
}

/* accu variable names */
string        accuInitial = accuPrefix + "0";
inline string accuFinal (word thread)
{
  return accuPrefix + to_string(thread) + "_FINAL";
}
inline string accuVar (unsigned long step, word thread)
{
  return accuPrefix + to_string(step) + '_' + to_string(thread);
}

/* machine memory variable names */
string        heapInitial = heapPrefix + "0";
string        heapFinal = heapPrefix + "FINAL";
inline string heapVar (unsigned long step)
{
  return heapPrefix + to_string(step);
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
    << setw(word_size / 4)
    << hex
    << val;

  return s.str();
}

/*******************************************************************************
 * SMT-Lib v2.5 Program Encoder Class
 ******************************************************************************/
smtlib::Encoder::Encoder (ProgramList & p, unsigned long b) :
  programs(p),
  bound(b)
{
  if (!programs.empty())
    encode();
}

/* smtlib::Encoder::encode (void) *********************************************/
void smtlib::Encoder::encode ()
{
  /* add file header */
  addHeader();

  /* add variable declarations */
  addThreadDeclarations();
  addStmtDeclarations();
  addMemDeclarations();
  addAccuDeclarations();
  addHeapDeclarations();
  addExitDeclarations();

  /* add cardinality constraints for thread activation per step */
  addThreadConstraints();

  /* encode programs */
  for (thread = 0; thread < programs.size(); thread++)
    encodeProgram();
}

/* smtlib::Encoder::encodeProgram (void) **************************************/
void smtlib::Encoder::encodeProgram ()
{
  formula << setw(80) << setfill(';') << ';' << endl;
  formula << "; Thread " + to_string(thread) + " " << endl;
  formula << setw(80) << setfill(';') << ';' << endl;
  formula << endl;

  /* the program to encode */
  Program & program = *programs[thread];

  /* last pc in program */
  word lastPc = program.size() - 1;

  /* find jump targets */
  collectPredecessors();

  /* activate initial program statement */
  formula << "; activate initial program statement" << endl;
  formula << smtlib::assert(stmtVar(1, thread, 0)) << endl << endl;

  /* encode the program */
  for (step = 1; step <= bound; step++)
    {
      formula << left
              << setw(80)
              << setfill(';')
              << ("; step " + to_string(step) + " ")
              << endl;

      unsigned long prevStep = step - 1;

      for (pc = 0; pc <= lastPc; pc++)
        {
          const bool isFinal =
                        step == bound ||
                        pc == lastPc ||
                        dynamic_pointer_cast<Exit>(program[pc]);

          formula << "; " << program[pc]->getSymbol() << endl;

          /* assign current program state variables */
          cur.mem       = memVar(step, thread);
          cur.accu      = accuVar(step, thread);
          cur.heap      = heapVar(step);

          /* current thread active => activate statement */
          string curThread  = threadVar(step, thread);
          string curStmt    = stmtVar(step, thread, pc);

          cur.activator     = smtlib::land(curThread, curStmt);

          /* no predecessor for the very first program statement */
          if (step == 1 || predecessors[pc].empty())
            {
              /* dummy predecessors for first program statement */
              old.mem   = memInitial;
              old.accu  = accuInitial;
              old.heap  = heapInitial;

              program[pc]->encode(*this);
            }
          else
            {
              old.mem   = memVar(prevStep, thread);
              old.accu  = accuVar(prevStep, thread);
              old.heap  = heapVar(prevStep);

              program[pc]->encode(*this);
            }

          /* no more statements or bound reached? assign final variables */
          if (isFinal)
              assignFinal();

          formula << endl;

          /* current thread disabled => preserve program / thread state */
          formula << "; preserve program state if thread wasn't active" << endl;
          cur.activator = smtlib::lnot(threadVar(step, thread));
          restoreMem();
          restoreAccu();
          activate(cur.activator, stmtVar(step + 1, thread, pc));

          formula << endl;
        }
    }
}

/* smtlib::Encoder::collectPredecessors (void) ********************************/
void smtlib::Encoder::collectPredecessors ()
{
  predecessors.clear();

  word length = programs[thread]->size();

  for (pc = 0; pc < length; pc++)
    {
      /* add previous statement if pc > 0 */
      if (pc > 0)
        predecessors[pc].insert(pc - 1);

      /* add current pc to predecessors of target statement */
      /* NOTE: possible improvement: remove pc of JMP from successor before
       * adding to the target statement */
      if (JmpPtr j = dynamic_pointer_cast<Jmp>(programs[thread]->at(pc)))
        predecessors[j->arg].insert(pc);
    }
}

/* smtlib::Encoder::addHeader (void) ******************************************/
void smtlib::Encoder::addHeader ()
{
  formula << "; bound: " << bound << endl;
  formula << "; programs: " << endl;

  for (thread = 0; thread < programs.size(); thread++)
    formula << ";   " << to_string(thread) << ": "
            << programs[thread]->path << endl;

  formula << endl;

  /* add logic definition */
  formula << smtlib::setLogic() << endl << endl;
}

/* smtlib::Encoder::addThreadDeclarations (void) ******************************/
void smtlib::Encoder::addThreadDeclarations ()
{
  formula << "; thread activation - THREAD_<step>_<thread>" << endl;

  word numThreads = programs.size();

  for (step = 1; step <= bound; step++)
    for (thread = 0; thread < numThreads; thread++)
      formula << smtlib::declareVar(threadVar(step, thread), "Bool") << endl;

  formula << endl;

  /* final thread variables */
  formula << smtlib::declareVar(threadFinal, "Bool") << endl;

  formula << endl;
}

/* smtlib::Encoder::addStmtDeclarations (void) ********************************/
void smtlib::Encoder::addStmtDeclarations ()
{
  formula << "; program statement activation - STMT_<step>_<thread>_<pc>"
          << endl;

  word numThreads = programs.size();

  for (step = 1; step <= bound; step++)
    for (thread = 0; thread < numThreads; thread++)
      for (pc = 0; pc < programs[thread]->size(); pc++)
        formula << smtlib::declareVar(stmtVar(step, thread, pc), "Bool")
                << endl;

  formula << endl;

  /* final statement variable */
  for (thread = 0; thread < numThreads; thread++)
    formula << smtlib::declareVar(stmtFinal(thread), "Bool") << endl;

  formula << endl;
}

/* smtlib::Encoder::addMemDeclerations (void) *********************************/
void smtlib::Encoder::addMemDeclarations ()
{
  formula << "; cas memory register - MEM_<step>_<thread>" << endl;

  /* initial mem variable */
  formula << smtlib::declareVar(memInitial, bitvecWord) << endl;

  word numThreads = programs.size();

  for (step = 1; step <= bound; step++)
    for (thread = 0; thread < numThreads; thread++)
      formula << smtlib::declareVar(memVar(step, thread), bitvecWord) << endl;

  formula << endl;

  /* final mem variable */
  for (thread = 0; thread < numThreads; thread++)
    formula << smtlib::declareVar(memFinal(thread), bitvecWord) << endl;

  formula << endl;
}

/* smtlib::Encoder::addAccuDeclarations (void) ********************************/
void smtlib::Encoder::addAccuDeclarations ()
{
  formula << "; accumulator - ACCU_<step>_<thread>" << endl;

  word numThreads = programs.size();

  /* initial accu variable */
  formula << smtlib::declareVar(accuInitial, bitvecWord) << endl;
  formula << smtlib::assert(smtlib::equality(accuInitial, word2Hex(0))) << endl;

  for (step = 1; step <= bound; step++)
    for (thread = 0; thread < numThreads; thread++)
      formula << smtlib::declareVar(accuVar(step, thread), bitvecWord) << endl;

  formula << endl;

  /* final accu variable */
  for (thread = 0; thread < numThreads; thread++)
    formula << smtlib::declareVar(accuFinal(thread), bitvecWord) << endl;

  formula << endl;
}

/* smtlib::Encoder::addHeapDeclarations (void) ********************************/
void smtlib::Encoder::addHeapDeclarations ()
{
  formula << "; machine memory - HEAP_<step>" << endl;

  /* initial heap variable */
  formula <<  smtlib::declareVar(
                heapInitial,
                smtlib::array(bitvecWord, bitvecWord))
          <<  endl;

  for (step = 1; step <= bound; step++)
    formula <<  smtlib::declareVar(
                  heapVar(step),
                  smtlib::array(bitvecWord, bitvecWord))
            <<  endl;

  formula << endl;

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

/* smtlib::Encoder::addThreadConstraints (void) *******************************/
void smtlib::Encoder::addThreadConstraints ()
{
  formula << "; thread constraints (exactly one active at any step)" << endl;

  word numThreads = programs.size();

  if (numThreads == 1)
    {
      for (step = 1; step <= bound; step++)
        formula << smtlib::assert(threadVar(step, 0)) << endl;

      formula << endl;
    }
  /* generate naive pairwise constraints */
  else
    for (step = 1; step <= bound; step++)
      {
        for (thread = 0; thread < numThreads; thread++)
          for (word other = thread + 1; other < numThreads; other++)
            formula <<  smtlib::assert(
                          smtlib::lor(
                            smtlib::lnot(threadVar(step, thread)),
                            smtlib::lnot(threadVar(step, other))))
                    <<  endl;

        formula << endl;
      }
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
  string stmt = stmtVar(step, thread, pc);

  formula <<  endl
          <<  imply(stmt, stmtFinal(thread)) << endl
          <<  imply(stmt, smtlib::equality(memFinal(thread), cur.mem)) << endl
          <<  imply(stmt, smtlib::equality(accuFinal(thread), cur.accu)) << endl
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
  if (pc < programs[thread]->size() - 1)
    activate(cur.activator, stmtVar(step + 1, thread, pc + 1));
}

/* smtlib::Encoder::activateJump (string, string) *****************************/
inline void smtlib::Encoder::activateJump (string condition, word target)
{
  activate(
    smtlib::land(cur.activator, condition),
    stmtVar(step + 1, thread, target));

  if (pc < programs[thread]->size() - 1)
    activate(
      smtlib::land(
        cur.activator,
        smtlib::lnot(condition)),
      stmtVar(step + 1, thread, pc + 1));
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
  activate(cur.activator, stmtVar(step + 1, thread, j.arg));
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
          to_string(word_size - 1),
          to_string(word_size - 1),
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
          to_string(word_size - 1),
          to_string(word_size - 1),
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
            to_string(word_size - 1),
            to_string(word_size - 1),
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
