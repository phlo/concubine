#include "program.hh"

#include <iostream>

using namespace std;

/* default constructor ********************************************************/
Program::Program() {}

/* construct from file ********************************************************/
Program::Program(string & p) : path(p), syncIDs(), labels()
{
  Parser<Program> parser(p);
  parser.parse(this);
}

/* Program::add (InstructionPtr) **********************************************/
void Program::add (InstructionPtr i)
{
  push_back(i);

  /* collect sync barrier ids */
  if (SyncPtr s = dynamic_pointer_cast<Sync>(i))
    syncIDs.insert(s->arg);
}

/* Program::getPath (void) ****************************************************/
string & Program::getPath () { return path; }

/* Program::getSyncIDs (void) *************************************************/
unordered_set<word> & Program::getSyncIDs () { return syncIDs; }

/* Program::getLabels (void) **************************************************/
unordered_map<word, string> & Program::getLabels () { return labels; }

/* Program::print (bool) ******************************************************/
void Program::print (bool includePC)
{
  for (word i = 0; i < size(); i++)
    {
      print(includePC, i);
      cout << endl;
    }
}

/* Program::print (bool, word) ************************************************/
void Program::print (bool includePC, word pc)
{
  /* check if instruction can be referenced by a label */
  if (labels.find(pc) != labels.end())
    {
      cout << labels[pc];

      if (includePC)
        cout << "\t";
      else
        cout << ": ";
    }
  else if (includePC)
    cout << pc << "\t";

  /* instruction symbol */
  InstructionPtr cmd = at(pc);
  cout << cmd->getSymbol() << "\t";

  /* print unary instruction's argument */
  if (UnaryInstructionPtr u = dynamic_pointer_cast<UnaryInstruction>(cmd))
    {
      if (dynamic_pointer_cast<Jmp>(cmd) && labels.find(u->arg) != labels.end())
        cout << labels[u->arg];
      else
        cout << u->arg;
    }
}

/* Program::unroll (word) *****************************************************/
ProgramPtr Program::unroll (word iterations)
{
  /* unrolled program */
  ProgramPtr unrolled = make_shared<Program>();

  /* number of unrolled loops */
  unsigned num_loops = 0;

  /* maps old target pc to the list of forward jumps to that location */
  unordered_map<word, deque<JmpPtr>> forwardJumps;

  for (word i = 0; i < size(); i++)
    {
      /* adjust forward jumps to the current instruction */
      if (forwardJumps.find(i) != forwardJumps.end())
        {
          word target = unrolled->size();

          for (JmpPtr jmp : forwardJumps[i])
            {
              /* dirty hack: change value of const arg */
              word * arg = const_cast<word *>(&(jmp->arg));
              *arg = target;
            }

          /* copy label if present */
          if (labels.find(i) != labels.end())
            unrolled->labels[target] = labels[i];
        }

      /* instruction is a jump */
      if (JmpPtr jmp = dynamic_pointer_cast<Jmp>(at(i)))
        {
          /* unroll: backwards jump - loop found */
          if (jmp->arg < i)
            {
              /* flag to indicate a normal JMP (infinite loop) */
              bool isJMP = false;

              /* calculate pc of 1st instruction after loop */
              word outside = i + (iterations - 1) * (i - jmp->arg + 1) + 2;

              /* find inverse condition to exit the loop prematurely */
              JmpPtr negatedJmp = nullptr;

              /* addition for JNZNS: negation requires 2 jumps */
              JmpPtr nznsJmp = nullptr;

              if (dynamic_pointer_cast<Jz>(jmp)) /* JZ => JNZ */
                {
                  negatedJmp = make_shared<Jnz>(outside);
                }
              else if (dynamic_pointer_cast<Jnz>(jmp)) /* JNZ => JZ */
                {
                  negatedJmp = make_shared<Jz>(outside);
                }
              else if (dynamic_pointer_cast<Js>(jmp)) /* JS => JNS */
                {
                  negatedJmp = make_shared<Jns>(outside);
                }
              else if (dynamic_pointer_cast<Jns>(jmp)) /* JNS => JS */
                {
                  negatedJmp = make_shared<Js>(outside);
                }
              else if (dynamic_pointer_cast<Jnzns>(jmp)) /* JNZNS => JZ v JS */
                {
                  /* adjust outside pc for double jump */
                  outside += iterations - 1;

                  negatedJmp = make_shared<Js>(outside);

                  /* add extra jz */
                  nznsJmp = make_shared<Jz>(outside);
                }
              else /* JMP => ∞ */
                isJMP = true;

              /* add early exit only in case of conditional jump */
              if (!isJMP)
                {
                  /* add initial check */
                  unrolled->add(negatedJmp);

                  if (nznsJmp)
                    unrolled->add(nznsJmp);

                  /* add label */
                  unrolled->labels[outside] = "BREAK_" + to_string(num_loops++);
                }

              /* unroll loop */
              for (word iter = 1; iter < iterations; iter++)
                {
                  /* copy body */
                  for (word pc = jmp->arg; pc < i; pc++)
                    unrolled->add(at(pc));

                  if (!isJMP)
                    {
                      /* add inverse jump to exit the loop */
                      unrolled->add(negatedJmp);

                      if (nznsJmp)
                        unrolled->add(nznsJmp);
                    }
                }

              /* add exit statement if condition was never met */
              if (!isJMP)
                unrolled->add(make_shared<Exit>(1));
            }
          /* forward jump - adjust target pc */
          else
            {
              /* add unaltered forward jump */
              unrolled->add(jmp);

              /* save it to be adjusted later on */
              forwardJumps[jmp->arg].push_back(jmp);
            }
        }
      /* no jump - just copy instruction */
      else
        unrolled->add(at(i));
    }

  /* no loops - program ununrollable */
  if (size() == unrolled->size()) throw "no loops in program";

  return unrolled;
}
