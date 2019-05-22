#include "instructionset.hh"

#include <iostream>

#include "encoder.hh"
#include "simulator.hh"

using namespace std;

/*******************************************************************************
 * Instruction
 ******************************************************************************/
unordered_map<string, Instruction *(*)()>
  Instruction::Set::nullary_factory;

unordered_map<string, Instruction *(*)(const word)>
  Instruction::Set::unary_factory;

unordered_map<string, Instruction *(*)(const word, const bool)>
  Instruction::Set::memory_factory;

bool Instruction::Set::contains (const string name)
{
  if (nullary_factory.find(name) != nullary_factory.end())
    return true;

  if (unary_factory.find(name) != unary_factory.end())
    return true;

  if (memory_factory.find(name) != memory_factory.end())
    return true;

  return false;
}

Instruction_ptr Instruction::Set::create (const string && name)
{
  if (nullary_factory.find(name) == nullary_factory.end())
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr(nullary_factory[name]());
}

Instruction_ptr Instruction::Set::create (const string && name, const word arg)
{
  if (unary_factory.find(name) == unary_factory.end())
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr(unary_factory[name](arg));
}

Instruction_ptr Instruction::Set::create (
                                          const string && name,
                                          const word arg,
                                          const bool indirect
                                         )
{
  if (memory_factory.find(name) == memory_factory.end())
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr(memory_factory[name](arg, indirect));
}

/*******************************************************************************
 * Unary
 ******************************************************************************/
Unary::Unary (const word a) : arg(a) {}

/*******************************************************************************
 * Memory
 ******************************************************************************/
Memory::Memory (const word a, const bool i) : Unary(a), indirect(i) {}

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Instruction & a, const Instruction & b)
{
  if (a.symbol() != b.symbol())
    return false;

  if (a.type() != b.type())
    return false;

  using unary_ptr = const Unary *;
  using memory_ptr = const Memory *;

  if (memory_ptr ma = dynamic_cast<memory_ptr>(&a))
    {
      memory_ptr mb = dynamic_cast<memory_ptr>(&b);

      if (ma->arg != mb->arg && ma->indirect != mb->indirect)
        return false;
    }
  else if (unary_ptr ua = dynamic_cast<unary_ptr>(&a))
    {
      unary_ptr ub = dynamic_cast<unary_ptr>(&b);

      if (ua->arg != ub->arg)
        return false;
    }

  return true;
}

bool operator != (const Instruction & a, const Instruction & b)
{
  return !(a == b);
}

/*******************************************************************************
 * Machine Instructions
 *
 * use preprocessor to simplify definition of instructions
 * NOTE: Instruction::execute and Instruction::encode defined outside!
 ******************************************************************************/
#define DEFINE_MEMBERS(classname, types) \
  const Instruction::Type classname::_type = types; \
  \
  Instruction::Type classname::type () const { return classname::_type; } \
  const string & classname::symbol () const { return classname::_symbol; } \
  \
  void classname::execute (Thread & thread) { return thread.execute(*this); } \
  string classname::encode (Encoder & formula) { return formula.encode(*this); }

#define DEFINE_NULLARY(classname, symbol, types) \
  DEFINE_MEMBERS (classname, types) \
  const string classname::_symbol = [] (string sym) -> const string { \
    Instruction::Set::nullary_factory[sym] = \
      [] () -> Instruction * \
      { return new classname; }; \
    return sym; \
  }(symbol);

#define DEFINE_UNARY(classname, symbol, types) \
  DEFINE_MEMBERS(classname, types) \
  const string classname::_symbol = [] (string sym) -> const string { \
    Instruction::Set::unary_factory[sym] = \
      [] (const word a) -> Instruction * \
      { return new classname(a); }; \
    return sym; \
  }(symbol);

#define DEFINE_MEMORY(classname, symbol, types) \
  DEFINE_MEMBERS(classname, types) \
  const string classname::_symbol = [] (string sym) -> const string { \
    Instruction::Set::unary_factory[sym] = \
      [] (const word a) -> Instruction * \
      { return new classname(a); }; \
    Instruction::Set::memory_factory[sym] = \
      [] (const word a, const bool i) -> Instruction * \
      { return new classname(a, i); }; \
    return sym; \
  }(symbol);

DEFINE_MEMORY   (Load,  "LOAD",   accu | read)
DEFINE_MEMORY   (Store, "STORE",  write)

DEFINE_NULLARY  (Fence, "FENCE",  barrier)

DEFINE_MEMORY   (Add,   "ADD",    accu | read)
DEFINE_UNARY    (Addi,  "ADDI",   accu)
DEFINE_MEMORY   (Sub,   "SUB",    accu | read)
DEFINE_UNARY    (Subi,  "SUBI",   accu)

DEFINE_MEMORY   (Cmp,   "CMP",    accu | read)
DEFINE_UNARY    (Jmp,   "JMP",    none)
DEFINE_UNARY    (Jz,    "JZ",     none)
DEFINE_UNARY    (Jnz,   "JNZ",    none)
DEFINE_UNARY    (Js,    "JS",     none)
DEFINE_UNARY    (Jns,   "JNS",    none)
DEFINE_UNARY    (Jnzns, "JNZNS",  none)

DEFINE_MEMORY   (Mem,   "MEM",    accu | mem | read)
DEFINE_MEMORY   (Cas,   "CAS",    accu | read | write | atomic)

DEFINE_UNARY    (Check, "CHECK",  barrier)

DEFINE_NULLARY  (Halt,  "HALT",   none)
DEFINE_UNARY    (Exit,  "EXIT",   none)
