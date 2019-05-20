#include "instructionset.hh"

#include <iostream>

#include "encoder.hh"
#include "simulator.hh"
#include "thread.hh"

using namespace std;

/*******************************************************************************
 * Instruction::Attributes
 ******************************************************************************/
// const unsigned char Instruction::Attributes::ALTERS_HEAP = 1 << 0;
// const unsigned char Instruction::Attributes::ALTERS_ACCU = 1 << 1;
// const unsigned char Instruction::Attributes::ALTERS_MEM  = 1 << 2;

/*******************************************************************************
 * Instruction::Set
 ******************************************************************************/
unordered_map<string, Instruction *(*)()>
  Instruction::Set::nullary_factory;

unordered_map<string, Instruction *(*)(const word)>
  Instruction::Set::unary_factory;

unordered_map<string, Instruction *(*)(const word, const bool)>
  Instruction::Set::memory_factory;

Instruction::Type Instruction::Set::contains (const string name)
{
  if (nullary_factory.find(name) != nullary_factory.end())
    return Type::NULLARY;

  if (memory_factory.find(name) != memory_factory.end())
    return Type::MEMORY;

  if (unary_factory.find(name) != unary_factory.end())
    return Type::UNARY;

  return Instruction::Type::UNKNOWN;
}

Instruction_ptr Instruction::Set::create (const string name)
{
  if (!contains(name))
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr(nullary_factory[name]());
}

Instruction_ptr Instruction::Set::create (const string name, const word arg)
{
  if (!contains(name))
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr(unary_factory[name](arg));
}

Instruction_ptr Instruction::Set::create (
                                          const string name,
                                          const word arg,
                                          const bool indirect
                                         )
{
  if (!contains(name))
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr(memory_factory[name](arg, indirect));
}

/*******************************************************************************
 * Instruction
 ******************************************************************************/
Instruction::Type Instruction::type () const
{
  return Instruction::Type::NULLARY;
}

/*******************************************************************************
 * Unary
 ******************************************************************************/
Unary::Unary (const word a) : arg(a) {}

Instruction::Type Unary::type () const
{
  return Instruction::Type::UNARY;
}

/*******************************************************************************
 * Memory
 ******************************************************************************/
Memory::Memory (const word a, const bool i) : Unary(a), indirect(i) {}

Instruction::Type Memory::type () const
{
  return Instruction::Type::MEMORY;
}

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Instruction & a, const Instruction & b)
{
  if (a.symbol() != b.symbol())
    return false;

  using memory_ptr = const Memory *;

  if (memory_ptr _a = dynamic_cast<memory_ptr>(&a))
    if (memory_ptr _b = dynamic_cast<memory_ptr>(&b))
      return _a->arg == _b->arg && _a->indirect == _b->indirect;

  using unary_ptr = const Unary *;

  if (unary_ptr _a = dynamic_cast<unary_ptr>(&a))
    if (unary_ptr _b = dynamic_cast<unary_ptr>(&b))
      return _a->arg == _b->arg;

  throw runtime_error("operator == failed");
}

bool operator != (const Instruction & a, const Instruction & b)
{
  return !(a == b);
}

/*******************************************************************************
 * Machine Instructions
 *
 * use preprocessor to simplify definition of instructions
 * NOTE: 'execute' defined outside!
 ******************************************************************************/
#define DEFINE_COMMON_INSTRUCTION_MEMBERS(classname, attr)    \
  const Instruction::Attribute classname::_attributes = attr; \
  Instruction::OPCode classname::opcode () const              \
    { return OPCode::classname; }                             \
  const string & classname::symbol () const                   \
    { return classname::_symbol; }                            \
  unsigned char classname::attributes () const                \
    { return classname::_attributes; }                        \
  string classname::encode (Encoder & formula)                \
    { return formula.encode(*this); }

#define DEFINE_INSTRUCTION_NULLARY(classname, identifier, attributes) \
  DEFINE_COMMON_INSTRUCTION_MEMBERS (classname, attributes)           \
  const string  classname::_symbol = [](string sym)->const string     \
  {                                                                   \
    Instruction::Set::nullary_factory[sym] = []()->Instruction *      \
      {                                                               \
        return new classname;                                         \
      };                                                              \
    return sym;                                                       \
  }(identifier);                                                      \

#define DEFINE_INSTRUCTION_UNARY(classname, identifier, attributes)   \
  DEFINE_COMMON_INSTRUCTION_MEMBERS(classname, attributes)            \
  const string  classname::_symbol = [](string sym)->const string     \
  {                                                                   \
    Instruction::Set::unary_factory[sym] =                            \
      [](const word a)->Instruction *                                 \
      {                                                               \
        return new classname(a);                                      \
      };                                                              \
    return sym;                                                       \
  }(identifier);                                                      \

#define DEFINE_INSTRUCTION_MEMORY(classname, identifier, attributes)  \
  DEFINE_COMMON_INSTRUCTION_MEMBERS(classname, attributes)            \
  const string  classname::_symbol = [](string sym)->const string     \
  {                                                                   \
    Instruction::Set::unary_factory[sym] =                            \
      [](const word a)->Instruction *                                 \
      {                                                               \
        return new classname(a);                                      \
      };                                                              \
    Instruction::Set::memory_factory[sym] =                           \
      [](const word a, const bool i)->Instruction *                   \
      {                                                               \
        return new classname(a, i);                                   \
      };                                                              \
    return sym;                                                       \
  }(identifier);                                                      \

/* LOAD ***********************************************************************/
DEFINE_INSTRUCTION_MEMORY(Load, "LOAD", Attributes::accu | Attributes::read)
void Load::execute (Thread & thread)
{
  thread.pc++;
  thread.accu = thread.load(arg, indirect);
}

/* STORE **********************************************************************/
DEFINE_INSTRUCTION_MEMORY(Store, "STORE", Attributes::write)
void Store::execute (Thread & thread)
{
  thread.pc++;
  thread.store(arg, thread.accu, indirect);
}

/* FENCE **********************************************************************/
DEFINE_INSTRUCTION_NULLARY(Fence, "FENCE", Attributes::barrier)
void Fence::execute (Thread & thread)
{
  thread.pc++;
}

/* ADD ************************************************************************/
DEFINE_INSTRUCTION_MEMORY(Add, "ADD", Attributes::accu | Attributes::read)
void Add::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += thread.load(arg, indirect);
}

/* ADDI ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Addi, "ADDI", Attributes::accu)
void Addi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu += arg;
}

/* SUB ************************************************************************/
DEFINE_INSTRUCTION_MEMORY(Sub, "SUB", Attributes::accu | Attributes::read)
void Sub::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= thread.load(arg, indirect);
}

/* SUBI ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Subi, "SUBI", Attributes::accu)
void Subi::execute (Thread & thread)
{
  thread.pc++;
  thread.accu -= arg;
}

/* CMP ************************************************************************/
DEFINE_INSTRUCTION_MEMORY(Cmp, "CMP", Attributes::accu | Attributes::read)
void Cmp::execute (Thread & thread)
{
  thread.pc++;
  thread.accu = static_cast<word>(
    static_cast<signed_word>(thread.accu) -
    static_cast<signed_word>(thread.load(arg, indirect))
  );
}

/* JMP ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jmp, "JMP", Attributes::none)
void Jmp::execute (Thread & thread)
{
  thread.pc = arg;
}

/* JZ *************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jz, "JZ", Attributes::none)
void Jz::execute (Thread & thread)
{
  if (thread.accu == 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JNZ ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jnz, "JNZ", Attributes::none)
void Jnz::execute (Thread & thread)
{
  if (thread.accu != 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JS *************************************************************************/
DEFINE_INSTRUCTION_UNARY(Js, "JS", Attributes::none)
void Js::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) < 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JNS ************************************************************************/
DEFINE_INSTRUCTION_UNARY(Jns, "JNS", Attributes::none)
void Jns::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) >= 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* JNZNS **********************************************************************/
DEFINE_INSTRUCTION_UNARY(Jnzns, "JNZNS", Attributes::none)
void Jnzns::execute (Thread & thread)
{
  if (static_cast<signed_word>(thread.accu) > 0)
    thread.pc = arg;
  else
    thread.pc++;
}

/* MEM ************************************************************************/
DEFINE_INSTRUCTION_MEMORY(
  Mem,
  "MEM",
  Attributes::accu |
  Attributes::mem |
  Attributes::read)
void Mem::execute (Thread & thread)
{
  Load::execute(thread);
  thread.mem = thread.accu;
}

/* CAS ************************************************************************/
DEFINE_INSTRUCTION_MEMORY(
  Cas,
  "CAS",
  Attributes::accu |
  Attributes::read |
  Attributes::write |
  Attributes::atomic)
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

/* CHECK **********************************************************************/
DEFINE_INSTRUCTION_UNARY(Check, "CHECK", Attributes::barrier)
void Check::execute (Thread & thread)
{
  thread.pc++;
  thread.sync = arg;
  thread.state = Thread::State::WAITING;
}

/* EXIT ***********************************************************************/
DEFINE_INSTRUCTION_UNARY(Exit, "EXIT", Attributes::none)
void Exit::execute (Thread & thread)
{
  thread.accu = arg;
  thread.state = Thread::State::EXITING;
}
