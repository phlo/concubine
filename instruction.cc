#include "instruction.hh"

#include <cassert>

#include "encoder.hh"
#include "simulator.hh"

namespace ConcuBinE {

//==============================================================================
// Model<POD>
//
// Instruction::Concept implementation
//==============================================================================

template <class POD>
constexpr bool is_nullary = std::is_base_of<Instruction::Nullary, POD>::value;

template <class POD>
constexpr bool is_unary = std::is_base_of<Instruction::Unary, POD>::value;

template <class POD>
constexpr bool is_memory = std::is_base_of<Instruction::Memory, POD>::value;

template <class POD>
constexpr bool is_jump = std::is_base_of<Instruction::Jmp, POD>::value;

template <class POD>
struct Model : Instruction::Concept
{
  using Type = Instruction::Type;

  POD pod;

  Model (const POD & p) : pod(p) {}
  // Model (const T && pod) : obj(move(pod)) {}

  std::unique_ptr<Concept> clone () const
    {
      return std::make_unique<Model<POD>>(pod);
    }

  bool is_nullary () const { return ConcuBinE::is_nullary<POD>; }
  bool is_unary () const { return ConcuBinE::is_unary<POD>; }
  bool is_memory () const { return ConcuBinE::is_memory<POD>; }
  bool is_jump () const { return ConcuBinE::is_jump<POD>; }

  bool requires_flush () const
    {
      return pod.type & (Type::write | Type::barrier);
    }

  const std::string & symbol () const { return pod.symbol; }

  uint8_t type () const { return pod.type; }
  void type (const uint8_t type) { pod.type = type; }

  word_t arg () const
    {
      if constexpr(ConcuBinE::is_unary<POD>)
        return pod.arg;
      else
        { assert(false); return 0; }
    }

  void arg (const word_t a [[maybe_unused]])
    {
      if constexpr(ConcuBinE::is_unary<POD>)
        pod.arg = a;
      else
        assert(false);
    }

  bool indirect () const
    {
      if constexpr(ConcuBinE::is_memory<POD>)
        return pod.indirect;
      else
        { assert(false); return false; }
    }

  void indirect (const bool i [[maybe_unused]])
    {
      if constexpr(ConcuBinE::is_memory<POD>)
        pod.indirect = i;
      else
        assert(false);
    }

  void execute (Simulator & s) const { s.execute(pod); }
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

// Instruction::is_nullary -----------------------------------------------------
//
bool Instruction::is_nullary (const std::string & symbol)
{
  return nullary_factory->find(symbol) != nullary_factory->end();
}

// Instruction::is_unary -------------------------------------------------------
//
bool Instruction::is_unary (const std::string & symbol)
{
  return unary_factory->find(symbol) != unary_factory->end();
}

// Instruction::is_memory ------------------------------------------------------
//
bool Instruction::is_memory (const std::string & symbol)
{
  return memory_factory->find(symbol) != memory_factory->end();
}

// Instruction::contains -------------------------------------------------------
//
bool Instruction::contains (const std::string & symbol)
{
  return is_nullary(symbol) || is_unary(symbol) || is_memory(symbol);
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

void Instruction::execute (Simulator & s) const { model->execute(s); }
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

} // namespace ConcuBinE
