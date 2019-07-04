#include "instruction.hh"

#include <cassert>

#include "encoder.hh"
#include "simulator.hh"

//==============================================================================
// Model<T>
//
// Instruction::Concept implementation
//==============================================================================

template <class T>
struct Model : Instruction::Concept
{
  using Type = Instruction::Type;
  using Nullary = Instruction::Nullary;
  using Unary = Instruction::Unary;
  using Memory = Instruction::Memory;

  T pod;

  Model (const T & p) : pod(p) {}
  // Model (const T && pod) : obj(move(pod)) {}

  std::unique_ptr<Concept> clone () const
    {
      return std::make_unique<Model<T>>(pod);
    }

  bool is_nullary () const { return std::is_base_of<Nullary, T>::value; }
  bool is_unary () const { return std::is_base_of<Unary, T>::value; }
  bool is_memory () const { return std::is_base_of<Memory, T>::value; }
  bool is_jump () const { return pod.type & Instruction::Type::jump; }

  bool requires_flush () const
    {
      return pod.type & (Type::write | Type::barrier);
    }

  const std::string & symbol () const { return pod.symbol; }

  uint8_t type () const { return pod.type; }
  void type (const uint8_t type) { pod.type = type; }

  word_t arg () const
    {
      if constexpr(std::is_base_of<Unary, T>::value)
        return pod.arg;
      else
        { assert(false); return 0; }
    }

  void arg (const word_t a [[maybe_unused]])
    {
      if constexpr(std::is_base_of<Unary, T>::value)
        pod.arg = a;
      else
        assert(false);
    }

  bool indirect () const
    {
      if constexpr(std::is_base_of<Memory, T>::value)
        return pod.indirect;
      else
        { assert(false); return false; }
    }

  void indirect (const bool i [[maybe_unused]])
    {
      if constexpr(std::is_base_of<Memory, T>::value)
        pod.indirect = i;
      else
        assert(false);
    }

  void execute (Thread & t) const { t.execute(pod); }
  std::string encode (Encoder & e) const { return e.encode(pod); }
};

//==============================================================================
// Instruction
//==============================================================================

//------------------------------------------------------------------------------
// static members
//------------------------------------------------------------------------------

std::unique_ptr<Instruction::nullary_factory_map> Instruction::nullary_factory;
std::unique_ptr<Instruction::unary_factory_map> Instruction::unary_factory;
std::unique_ptr<Instruction::memory_factory_map> Instruction::memory_factory;

//------------------------------------------------------------------------------
// static member functions
//------------------------------------------------------------------------------

// Instruction::contains -------------------------------------------------------
//
bool Instruction::contains (const std::string & symbol)
{
  if (nullary_factory->find(symbol) != nullary_factory->end())
    return true;

  if (unary_factory->find(symbol) != unary_factory->end())
    return true;

  if (memory_factory->find(symbol) != memory_factory->end())
    return true;

  return false;
}

// Instruction::add_nullary ----------------------------------------------------
//
template <class POD>
const std::string & Instruction::add_nullary (const std::string & symbol,
                                              uint8_t type)
{
  if (!nullary_factory)
    nullary_factory = std::make_unique<nullary_factory_map>();

  return
    nullary_factory->emplace(
      std::move(symbol),
      [type] () { return Instruction(POD{type}); })
    .first->first;
}

// Instruction::add_unary ------------------------------------------------------
//
template <class POD>
const std::string & Instruction::add_unary (const std::string & symbol,
                                            uint8_t type)
{
  if (!unary_factory)
    unary_factory = std::make_unique<unary_factory_map>();

  return
    unary_factory->emplace(
      std::move(symbol),
      [type] (word_t a) { return Instruction(POD{type, a}); })
    .first->first;
}

// Instruction::add_memory -----------------------------------------------------
//
template <class POD>
const std::string & Instruction::add_memory (const std::string & symbol,
                                             uint8_t type)
{
  add_unary<POD>(symbol, type);

  if (!memory_factory)
    memory_factory = std::make_unique<memory_factory_map>();

  return
    memory_factory->emplace(
      std::move(symbol),
      [type] (word_t a, bool i) { return Instruction(POD{type, a, i}); })
    .first->first;
}

// Instruction::create ---------------------------------------------------------
//
Instruction Instruction::create (const std::string & symbol)
{
  if (nullary_factory->find(symbol) == nullary_factory->end())
    throw std::runtime_error("Instruction '" + symbol + "' unknown");

  return (*nullary_factory)[symbol]();
}

Instruction Instruction::create (const std::string & symbol, const word_t arg)
{
  if (unary_factory->find(symbol) == unary_factory->end())
    throw std::runtime_error("Instruction '" + symbol + "' unknown");

  return (*unary_factory)[symbol](arg);
}

Instruction Instruction::create (const std::string & symbol,
                                 const word_t arg,
                                 const bool indirect)
{
  if (memory_factory->find(symbol) == memory_factory->end())
    throw std::runtime_error("Instruction '" + symbol + "' unknown");

  return (*memory_factory)[symbol](arg, indirect);
}

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

template <class POD>
Instruction::Instruction (const POD & pod) :
  model(std::make_unique<Model<POD>>(pod))
{}

Instruction::Instruction (const Instruction & other) :
  model(other.model->clone())
{}

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

bool Instruction::is_nullary () const { return model->is_nullary(); }
bool Instruction::is_unary () const { return model->is_unary(); }
bool Instruction::is_memory () const { return model->is_memory(); }
bool Instruction::is_jump () const { return model->is_jump(); }

bool Instruction::requires_flush () const { return model->requires_flush(); }

const std::string & Instruction::symbol () const { return model->symbol(); }

uint8_t Instruction::type () const { return model->type(); }
void Instruction::type (uint8_t t) { model->type(t); }

word_t Instruction::arg () const { return model->arg(); }
void Instruction::arg (const word_t a) { model->arg(a); }

bool Instruction::indirect () const { return model->indirect(); }
void Instruction::indirect (const bool i) { model->indirect(i); }

void Instruction::execute (Thread & t) const { model->execute(t); }
std::string Instruction::encode (Encoder & e) const { return model->encode(e); }

//------------------------------------------------------------------------------
// member operators
//------------------------------------------------------------------------------

// assignment ------------------------------------------------------------------
//
Instruction & Instruction::operator = (const Instruction & other)
{
  model = other.model->clone();
  return *this;
}

//==============================================================================
// non-member operators
//==============================================================================

// equality --------------------------------------------------------------------
//
bool operator == (const Instruction & a, const Instruction & b)
{
  if (&a.symbol() != &b.symbol())
    return false;

  if (a.type() != b.type())
    return false;

  if (a.is_memory() && b.is_memory())
    return a.arg() == b.arg() && a.indirect() == b.indirect();

  if (a.is_unary() && b.is_unary())
    return a.arg() == b.arg();

  return true;
}

bool operator != (const Instruction & a, const Instruction & b)
{
  return !(a == b);
}
