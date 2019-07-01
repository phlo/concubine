#include "instructionset.hh"

#include <iostream>

#include "encoder.hh"
#include "simulator.hh"

using namespace std;

/*******************************************************************************
 * Instruction
 ******************************************************************************/
unique_ptr<unordered_map<string, Instruction *(*)()>>
  Instruction::Set::nullary_factory;
    // make_unique<unordered_map<string, Instruction *(*)()>>();

unique_ptr<unordered_map<string, Instruction *(*)(const word_t)>>
  Instruction::Set::unary_factory;
    // make_unique<unordered_map<string, Instruction *(*)(const word_t)>>();

unique_ptr<unordered_map<string, Instruction *(*)(const word_t, const bool)>>
  Instruction::Set::memory_factory;
    // make_unique<unordered_map<string, Instruction *(*)(const word_t, const bool)>>();

bool Instruction::Set::contains (const string name)
{
  if (nullary_factory->find(name) != nullary_factory->end())
    return true;

  if (unary_factory->find(name) != unary_factory->end())
    return true;

  if (memory_factory->find(name) != memory_factory->end())
    return true;

  return false;
}


/*
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
      [] (const word_t a) -> Instruction * \
      { return new classname(a); }; \
    return sym; \
  }(symbol);

#define DEFINE_MEMORY(classname, symbol, types) \
  DEFINE_MEMBERS(classname, types) \
  const string classname::_symbol = [] (string sym) -> const string { \
    Instruction::Set::unary_factory[sym] = \
      [] (const word_t a) -> Instruction * \
      { return new classname(a); }; \
    Instruction::Set::memory_factory[sym] = \
      [] (const word_t a, const bool i) -> Instruction * \
      { return new classname(a, i); }; \
    return sym; \
  }(symbol);

template <class T>
string Instruction::Set::add (const string symbol)
{
  if (is_base_of<Unary, T>())
    {
      unary_factory[symbol] = [] (const word_t a) -> Instruction * { return new T(a); };
    }
  if (is_base_of<Memory, T>())
    {
      memory_factory[symbol] = [] (const word_t a, const bool i) -> Instruction * { return new T(a, i); };
    }
  else if (is_base_of<Instruction, T>())
    {
      nullary_factory[symbol] = [] () -> Instruction * { return new T(); };
    }

  return symbol;
}

template <typename T, typename enable_if<is_base_of<Instruction, T>() && !is_base_of(Unary, T>>::type>
string Instruction::Set::add (const string symbol)
{
  nullary_factory[symbol] = [] () -> Instruction * { return new T(); };

  return symbol;
}

template <typename T, typename enable_if<is_base_of<Instruction, T>() && !is_base_of(Memory, T>>::type>
string Instruction::Set::add (const string symbol)
{
  unary_factory[symbol] = [] (const word_t a) -> Instruction * { return new T(a); };

  return symbol;
}

template <typename T, typename enable_if<is_base_of<Instruction, T>() && is_base_of(Memory, T>>::type>
string Instruction::Set::add (const string symbol)
{
  unary_factory[symbol] = [] (const word_t a) -> Instruction * { return new T(a); };
  memory_factory[symbol] = [] (const word_t a, const bool i) -> Instruction * { return new T(a, i); };

  return symbol;
}
*/

template <class T>
string Instruction::Set::add_nullary (const string symbol)
{
  if (!nullary_factory)
    nullary_factory = make_unique<unordered_map<string, Instruction *(*)()>>();

  (*nullary_factory)[symbol] = [] () -> Instruction * { return new T(); };

  return symbol;
}

template <class T>
string Instruction::Set::add_unary (const string symbol)
{
  if (!unary_factory)
    unary_factory = make_unique<unordered_map<string, Instruction *(*)(const word_t)>>();

  (*unary_factory)[symbol] = [] (const word_t a) -> Instruction * { return new T(a); };

  return symbol;
}

template <class T>
string Instruction::Set::add_memory (const string symbol)
{
  add_unary<T>(symbol);

  if (!memory_factory)
    memory_factory = make_unique<unordered_map<string, Instruction *(*)(const word_t, const bool)>>();

  (*memory_factory)[symbol] = [] (const word_t a, const bool i) -> Instruction * { return new T(a, i); };

  return symbol;
}

Instruction_ptr Instruction::Set::create (const string & name)
{
  if (nullary_factory->find(name) == nullary_factory->end())
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr((*nullary_factory)[name]());
}

Instruction_ptr Instruction::Set::create (const string & name, const word_t arg)
{
  if (unary_factory->find(name) == unary_factory->end())
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr((*unary_factory)[name](arg));
}

Instruction_ptr Instruction::Set::create (
                                          const string & name,
                                          const word_t arg,
                                          const bool indirect
                                         )
{
  if (memory_factory->find(name) == memory_factory->end())
    throw runtime_error("Instruction '" + name + "' unknown");

  return Instruction_ptr((*memory_factory)[name](arg, indirect));
}

Instruction::Instruction (Type t) : type(t) {}

bool Instruction::requires_flush ()
{
  return type & (Types::write | Types::barrier);
}

/*******************************************************************************
 * Unary
 ******************************************************************************/
Unary::Unary (const Type t, const word_t a) : Instruction(t), arg(a) {}

/*******************************************************************************
 * Memory
 ******************************************************************************/
Memory::Memory (const Type t, const word_t a, const bool i) : Unary(t, a), indirect(i) {}

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Instruction & a, const Instruction & b)
{
  if (a.symbol() != b.symbol())
    return false;

  if (a.type != b.type)
    return false;

  using unary_ptr = const Unary *;
  using memory_ptr = const Memory *;

  if (memory_ptr ma = dynamic_cast<memory_ptr>(&a))
    {
      memory_ptr mb = dynamic_cast<memory_ptr>(&b);

      if (ma->arg != mb->arg || ma->indirect != mb->indirect)
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
#define DEFINE(classname) \
  const string & classname::symbol () const { return classname::_symbol; } \
  void classname::execute (Thread & thread) { return thread.execute(*this); } \
  string classname::encode (Encoder & formula) { return formula.encode(*this); }

DEFINE(Load)
DEFINE(Store)

DEFINE(Fence)

DEFINE(Add)
DEFINE(Addi)
DEFINE(Sub)
DEFINE(Subi)
DEFINE(Mul)
DEFINE(Muli)

DEFINE(Cmp)
DEFINE(Jmp)
DEFINE(Jz)
DEFINE(Jnz)
DEFINE(Js)
DEFINE(Jns)
DEFINE(Jnzns)

DEFINE(Mem)
DEFINE(Cas)

DEFINE(Check)

DEFINE(Halt)
DEFINE(Exit)
