#include "instructionset.hh"

#include <iostream>

#include "machine.hh"
#include "thread.hh"

/*******************************************************************************
 * InstructionSet
 ******************************************************************************/

unordered_map<string, Instruction *(*)()> InstructionSet::factory;


/*******************************************************************************
 * Instruction Base Classes
 ******************************************************************************/

void UnaryInstruction::setArg (int a) { arg = a; }

int UnaryInstruction::getArg () { return arg; }

void Instruction::printDebug (Thread & t)
{
  cout << "T" << t.id << ": " <<
    getSymbol() <<
    endl;
}

void UnaryInstruction::printDebug (Thread & t)
{
  cout << "T" << t.id << ": " <<
    getSymbol() << " " << getArg() <<
    endl;
}


/*******************************************************************************
 * used to simplify definition of instructions
 * NOTE: 'execute' defined outside!
 ******************************************************************************/
#define DEFINE_INSTRUCTION(classname, identifier)                     \
  const string  classname::symbol = [](string sym)->const string      \
  {                                                                   \
    InstructionSet::factory[sym] = []()->Instruction *                \
      {                                                               \
        return new classname;                                         \
      };                                                              \
    return sym;                                                       \
  }(identifier);                                                      \
  OPCode        classname::getOPCode () { return OPCode::classname; } \
  const string& classname::getSymbol () { return classname::symbol; }

/*******************************************************************************
 * Instructions
 ******************************************************************************/

/* EXIT ***********************************************************************/
DEFINE_INSTRUCTION(Exit, "EXIT")
void Exit::execute (Thread & thread)
{
  thread.state = Thread::State::EXITING;
}

/* HALT ***********************************************************************/
DEFINE_INSTRUCTION(Halt, "HALT")
void Halt::execute (Thread & thread)
{
  thread.state = Thread::State::STOPPED;
}

/* SYNC ***********************************************************************/
DEFINE_INSTRUCTION(Sync, "SYNC")
void Sync::execute (Thread & thread)
{
  thread.pc++;
  thread.sync = arg;
  thread.state = Thread::State::WAITING;
}

/* LOAD ***********************************************************************/
DEFINE_INSTRUCTION(Load, "LOAD")
void Load::execute (Thread & thread)
{
  thread.pc++;
  thread.accu = thread.load(arg);
}

/* STORE **********************************************************************/
DEFINE_INSTRUCTION(Store, "STORE")
void Store::execute (Thread & thread)
{
  thread.pc++;
  thread.store(arg, thread.accu);
}

/* ADD ************************************************************************/
DEFINE_INSTRUCTION(Add, "ADD")
void Add::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += thread.load(arg);
}

/* ADDI ***********************************************************************/
DEFINE_INSTRUCTION(Addi, "ADDI")
void Addi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += arg;
}

/* SUB ************************************************************************/
DEFINE_INSTRUCTION(Sub, "SUB")
void Sub::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= thread.load(arg);
}

/* SUBI ***********************************************************************/
DEFINE_INSTRUCTION(Subi, "SUBI")
void Subi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= arg;
}

/* CMP ************************************************************************/
DEFINE_INSTRUCTION(Cmp, "CMP")
void Cmp::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= thread.load(arg);
}

/* i'm just too lazy ... ******************************************************/
#define DEFINE_JUMP_EXECUTION(classname, predicate)                   \
  void classname::execute (Thread & t)                                \
  {                                                                   \
    t.pc = t.accu predicate 0 ? static_cast<size_t>(arg) : t.pc + 1;  \
  }

/* JZ *************************************************************************/
DEFINE_INSTRUCTION(Jz, "JZ")
DEFINE_JUMP_EXECUTION(Jz, ==)

/* JNZ ************************************************************************/
DEFINE_INSTRUCTION(Jnz, "JNZ")
DEFINE_JUMP_EXECUTION(Jnz, !=)

/* JL *************************************************************************/
DEFINE_INSTRUCTION(Jl, "JL")
DEFINE_JUMP_EXECUTION(Jl, <)

/* JLE ************************************************************************/
DEFINE_INSTRUCTION(Jle, "JLE")
DEFINE_JUMP_EXECUTION(Jle, <=)

/* JG *************************************************************************/
DEFINE_INSTRUCTION(Jg, "JG")
DEFINE_JUMP_EXECUTION(Jg, >)

/* JGE ************************************************************************/
DEFINE_INSTRUCTION(Jge, "JGE")
DEFINE_JUMP_EXECUTION(Jge, >=)

/* MEM ************************************************************************/
DEFINE_INSTRUCTION(Mem, "MEM")
void Mem::execute (Thread & thread)
{
  thread.pc++;
  thread.mem = thread.accu;
}

/* CAS ************************************************************************/
DEFINE_INSTRUCTION(Cas, "CAS")
void Cas::execute (Thread & thread)
{
  thread.pc++;

  short acutal = thread.load(arg);
  short expected = thread.mem;

  if (acutal == expected)
    {
      thread.store(arg, thread.accu);
      thread.accu = 0;
    }
  else
    {
      thread.accu = 1;  // TODO: reverse notification - like in C?
    }
}
