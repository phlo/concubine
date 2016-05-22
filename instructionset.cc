#include "instructionset.hh"

#include <iostream>

#include "machine.hh"

/*******************************************************************************
 * Instruction::Set
 ******************************************************************************/
unordered_map<string, Instruction *(*)()>
  Instruction::Set::nullaryFactory;

unordered_map<string, Instruction *(*)(const word)>
  Instruction::Set::unaryFactory;

Instruction::Type Instruction::Set::contains (string & name)
{
  if (nullaryFactory.find(name) != nullaryFactory.end())
    return Type::NULLARY;

  if (unaryFactory.find(name) != unaryFactory.end())
    return Type::UNARY;

  return Instruction::Type::UNKNOWN;
}

InstructionPtr Instruction::Set::create (string & name)
{
  return InstructionPtr(nullaryFactory[name]());
}

InstructionPtr Instruction::Set::create (string & name, const word arg)
{
  return InstructionPtr(unaryFactory[name](arg));
}

/*******************************************************************************
 * Instruction
 ******************************************************************************/
Instruction::Type Instruction::getType ()
{
  return Instruction::Type::NULLARY;
}

void Instruction::print (Thread & t)
{
  cout << t.id << "\t" << t.pc << "\t" <<
    getSymbol() <<
    endl;
}

/*******************************************************************************
 * UnaryInstruction
 ******************************************************************************/
UnaryInstruction::UnaryInstruction (const word a) : arg(a) {}

Instruction::Type UnaryInstruction::getType ()
{
  return Instruction::Type::UNARY;
}

void UnaryInstruction::print (Thread & t)
{
  cout << t.id << "\t" << t.pc << "\t" <<
    getSymbol() << "\t" << arg <<
    endl;
}

/*******************************************************************************
 * used to simplify definition of instructions
 * NOTE: 'execute' defined outside!
 ******************************************************************************/
#define DEFINE_COMMON_INSTRUCTION_MEMBERS(classname)                        \
  Instruction::OPCode classname::getOPCode () { return OPCode::classname; } \
  const string& classname::getSymbol () { return classname::symbol; }

#define DEFINE_INSTRUCTION_NULLARY(classname, identifier)           \
  DEFINE_COMMON_INSTRUCTION_MEMBERS (classname)                     \
  const string  classname::symbol = [](string sym)->const string    \
  {                                                                 \
    Instruction::Set::nullaryFactory[sym] = []()->Instruction *     \
      {                                                             \
        return new classname;                                       \
      };                                                            \
    return sym;                                                     \
  }(identifier);                                                    \

#define DEFINE_INSTRUCTION_UNARY(classname, identifier)                     \
  DEFINE_COMMON_INSTRUCTION_MEMBERS(classname)                              \
  const string  classname::symbol = [](string sym)->const string            \
  {                                                                         \
    Instruction::Set::unaryFactory[sym] = [](const word arg)->Instruction * \
      {                                                                     \
        return new classname(arg);                                          \
      };                                                                    \
    return sym;                                                             \
  }(identifier);                                                            \
classname::classname (const word a) : UnaryInstruction(a) {}

/*******************************************************************************
 * Machine Instructions
 ******************************************************************************/

/* EXIT ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Exit, "EXIT")
void Exit::execute (Thread & thread)
{
  thread.accu = arg;
  thread.state = Thread::State::EXITING;
}

/* HALT ***********************************************************************/
DEFINE_INSTRUCTION_NULLARY(Halt, "HALT")
void Halt::execute (Thread & thread)
{
  thread.state = Thread::State::STOPPED;
}

/* SYNC ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Sync, "SYNC")
void Sync::execute (Thread & thread)
{
  thread.pc++;
  thread.sync = arg;
  thread.state = Thread::State::WAITING;
}

/* LOAD ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Load, "LOAD")
void Load::execute (Thread & thread)
{
  thread.pc++;
  thread.accu = thread.load(arg);
}

/* STORE **********************************************************************/
DEFINE_INSTRUCTION_UNARY(Store, "STORE")
void Store::execute (Thread & thread)
{
  thread.pc++;
  thread.store(arg, thread.accu);
}

/* ADD ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Add, "ADD")
void Add::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += thread.load(arg);
}

/* ADDI ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Addi, "ADDI")
void Addi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += arg;
}

/* SUB ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Sub, "SUB")
void Sub::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= thread.load(arg);
}

/* SUBI ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Subi, "SUBI")
void Subi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= arg;
}

/* CMP ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Cmp, "CMP")
void Cmp::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= thread.load(arg);
}

/* i'm just too lazy ... ******************************************************/
#define DEFINE_JUMP_EXECUTION(classname, predicate) \
  void classname::execute (Thread & t)              \
  {                                                 \
    if (t.accu predicate 0)                         \
      t.pc = arg;                                   \
    else                                            \
      t.pc++;                                       \
  }

/* JZ *************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jz, "JZ")
DEFINE_JUMP_EXECUTION(Jz, ==)

/* JNZ ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jnz, "JNZ")
DEFINE_JUMP_EXECUTION(Jnz, !=)

/* JL *************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jl, "JL")
DEFINE_JUMP_EXECUTION(Jl, <)

/* JLE ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jle, "JLE")
DEFINE_JUMP_EXECUTION(Jle, <=)

/* JG *************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jg, "JG")
DEFINE_JUMP_EXECUTION(Jg, >)

/* JGE ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jge, "JGE")
DEFINE_JUMP_EXECUTION(Jge, >=)

/* MEM ************************************************************************/
DEFINE_INSTRUCTION_NULLARY(Mem, "MEM")
void Mem::execute (Thread & thread)
{
  thread.pc++;
  thread.mem = thread.accu;
}

/* CAS ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Cas, "CAS")
void Cas::execute (Thread & thread)
{
  thread.pc++;

  word acutal = thread.load(arg);
  word expected = thread.mem;

  if (acutal == expected)
    {
      thread.store(arg, thread.accu);
      thread.accu = 1;
    }
  else
    {
      thread.accu = 0;
    }
}
