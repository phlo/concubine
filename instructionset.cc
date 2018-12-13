#include "instructionset.hh"

#include <iostream>

#include "thread.hh"
#include "machine.hh"
#include "encoder.hh"

using namespace std;

/*******************************************************************************
 * Instruction::Set
 ******************************************************************************/
unordered_map<string, Instruction *(*)()>
  Instruction::Set::nullary_factory;

unordered_map<string, Instruction *(*)(const word)>
  Instruction::Set::unary_factory;

Instruction::Type Instruction::Set::contains (string name)
{
  if (nullary_factory.find(name) != nullary_factory.end())
    return Type::NULLARY;

  if (unary_factory.find(name) != unary_factory.end())
    return Type::UNARY;

  return Instruction::Type::UNKNOWN;
}

InstructionPtr Instruction::Set::create (string name)
{
  if (!contains(name))
    throw runtime_error("Instruction '" + name + "' unknown");

  return InstructionPtr(nullary_factory[name]());
}

InstructionPtr Instruction::Set::create (string name, const word arg)
{
  if (!contains(name))
    throw runtime_error("Instruction '" + name + "' unknown");

  return InstructionPtr(unary_factory[name](arg));
}


/*******************************************************************************
 * Instruction
 ******************************************************************************/

Instruction::Type Instruction::get_type ()
{
  return Instruction::Type::NULLARY;
}


/*******************************************************************************
 * UnaryInstruction
 ******************************************************************************/
UnaryInstruction::UnaryInstruction (const word a) : arg(a) {}

Instruction::Type UnaryInstruction::get_type ()
{
  return Instruction::Type::UNARY;
}


/*******************************************************************************
 * MemoryInstruction
 ******************************************************************************/
MemoryInstruction::MemoryInstruction (const word a) :
  UnaryInstruction(a),
  indirect(false)
{}


/*******************************************************************************
 * Machine Instructions
 *
 * use preprocessor to simplify definition of instructions
 * NOTE: 'execute' defined outside!
 ******************************************************************************/
#define DEFINE_COMMON_INSTRUCTION_MEMBERS(classname)                           \
  Instruction::OPCode classname::get_opcode () { return OPCode::classname; }   \
  const string& classname::get_symbol () { return classname::symbol; }         \
  string classname::encode (Encoder & formula) { return formula.encode(*this); }

#define DEFINE_INSTRUCTION_NULLARY(classname, identifier)           \
  DEFINE_COMMON_INSTRUCTION_MEMBERS (classname)                     \
  const string  classname::symbol = [](string sym)->const string    \
  {                                                                 \
    Instruction::Set::nullary_factory[sym] = []()->Instruction *    \
      {                                                             \
        return new classname;                                       \
      };                                                            \
    return sym;                                                     \
  }(identifier);                                                    \

#define DEFINE_INSTRUCTION_UNARY(classname, identifier)                     \
  DEFINE_COMMON_INSTRUCTION_MEMBERS(classname)                              \
  const string  classname::symbol = [](string sym)->const string            \
  {                                                                         \
    Instruction::Set::unary_factory[sym] = [](const word a)->Instruction *  \
      {                                                                     \
        return new classname(a);                                            \
      };                                                                    \
    return sym;                                                             \
  }(identifier);                                                            \

/* LOAD ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Load, "LOAD")
void Load::execute (Thread & thread)
{
  thread.pc++;
  thread.accu = thread.load(arg, indirect);
}

/* STORE **********************************************************************/
DEFINE_INSTRUCTION_UNARY(Store, "STORE")
void Store::execute (Thread & thread)
{
  thread.pc++;
  thread.store(arg, thread.accu, indirect);
}

/* ADD ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Add, "ADD")
void Add::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += thread.load(arg, indirect);
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
  thread.accu -= thread.load(arg, indirect);
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
  thread.accu = static_cast<word>(
    static_cast<signed_word>(thread.accu) -
    static_cast<signed_word>(thread.load(arg, indirect))
  );
}

/* JMP ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jmp, "JMP")
void Jmp::execute (Thread & thread)
{
  thread.pc = arg;
}

/* JZ *************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jz, "JZ")
void Jz::execute (Thread & thread)
{
  if (thread.accu == 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JNZ ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jnz, "JNZ")
void Jnz::execute (Thread & thread)
{
  if (thread.accu != 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JS *************************************************************************/
DEFINE_INSTRUCTION_UNARY(Js, "JS")
void Js::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) < 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JNS ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jns, "JNS")
void Jns::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) >= 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JNZNS **********************************************************************/
DEFINE_INSTRUCTION_UNARY(Jnzns, "JNZNS")
void Jnzns::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) > 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* MEM ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Mem, "MEM")
void Mem::execute (Thread & thread)
{
  Load::execute(thread);
  thread.mem = thread.accu;
}

/* CAS ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Cas, "CAS")
void Cas::execute (Thread & thread)
{
  thread.pc++;

  word acutal = thread.load(arg, indirect);
  word expected = thread.mem;

  if (acutal == expected)
    {
      thread.store(arg, thread.accu, indirect);
      thread.accu = 1;
    }
  else
    {
      thread.accu = 0;
    }
}

/* SYNC ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Sync, "SYNC")
void Sync::execute (Thread & thread)
{
  thread.pc++;
  thread.sync = arg;
  thread.state = Thread::State::WAITING;
}

/* EXIT ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Exit, "EXIT")
void Exit::execute (Thread & thread)
{
  thread.accu = arg;
  thread.state = Thread::State::EXITING;
}
