#include "instruction.hh"

#include <cassert>

#include "encoder.hh"
#include "simulator.hh"

//==============================================================================
// using declarations
//==============================================================================

using std::string;

using std::unique_ptr;
using std::make_unique;

using std::is_base_of;

using std::runtime_error;

//==============================================================================
// Instruction::Set
//==============================================================================

//------------------------------------------------------------------------------
// static members
//------------------------------------------------------------------------------

unique_ptr<Instruction::Set::nullary_t> Instruction::Set::nullary;
unique_ptr<Instruction::Set::unary_t> Instruction::Set::unary;
unique_ptr<Instruction::Set::memory_t> Instruction::Set::memory;

//------------------------------------------------------------------------------
// static member functions
//------------------------------------------------------------------------------

bool Instruction::Set::contains (const string & symbol)
{
  if (nullary->find(symbol) != nullary->end())
    return true;

  if (unary->find(symbol) != unary->end())
    return true;

  if (memory->find(symbol) != memory->end())
    return true;

  return false;
}

template <class POD>
const string & Instruction::Set::add_nullary (const string && symbol)
{
  if (!nullary)
    nullary = make_unique<nullary_t>();

  return
    nullary->emplace(
      symbol,
      [] () -> Instruction { return POD(); })
    .first->first;
}

template <class POD>
const string & Instruction::Set::add_unary (const string && symbol)
{
  if (!unary)
    unary = make_unique<unary_t>();

  return
    unary->emplace(
      symbol,
      [] (word_t a) -> Instruction { return POD(a); })
    .first->first;
}

template <class POD>
const string & Instruction::Set::add_memory (const string && symbol)
{
  add_unary<POD>(string {symbol});

  if (!memory)
    memory = make_unique<memory_t>();

  return
    memory->emplace(
      symbol,
      [] (word_t a, bool i) -> Instruction { return POD(a, i); })
    .first->first;
}

Instruction Instruction::Set::create (const string & symbol)
{
  if (nullary->find(symbol) == nullary->end())
    throw runtime_error("Instruction '" + symbol + "' unknown");

  return (*nullary)[symbol]();
}

Instruction Instruction::Set::create (const string & symbol, const word_t arg)
{
  if (unary->find(symbol) == unary->end())
    throw runtime_error("Instruction '" + symbol + "' unknown");

  return (*unary)[symbol](arg);
}

Instruction Instruction::Set::create (const string & symbol,
                                      const word_t arg,
                                      const bool indirect)
{
  if (memory->find(symbol) == memory->end())
    throw runtime_error("Instruction '" + symbol + "' unknown");

  return (*memory)[symbol](arg, indirect);
}

//==============================================================================
// Model<T>
//
// * Instruction::Concept implementation
//==============================================================================

template <class T>
struct Model : public Instruction::Concept
{
  using Nullary = Instruction::Nullary;
  using Unary = Instruction::Unary;
  using Memory = Instruction::Memory;

  T pod;

  Model (const T & p) : pod(p) {}
  // Model (const T && pod) : obj(move(pod)) {}

  virtual pointer clone () const { return make_unique<Model<T>>(pod); }

  virtual bool is_nullary () const { return is_base_of<Nullary, T>(); }
  virtual bool is_unary () const { return is_base_of<Unary, T>(); }
  virtual bool is_memory () const { return is_base_of<Memory, T>(); }
  virtual bool is_jump () const { return pod.type & Instruction::Type::jump; }

  virtual bool requires_flush () const
    {
      return pod.type & (Instruction::Type::write | Instruction::Type::barrier);
    }

  virtual const string & symbol () const { return pod.symbol; }

  virtual uint8_t type () const { return pod.type; }
  virtual void type (uint8_t type) { pod.type = type; }

  virtual word_t arg () const { const Unary & u = *this; return u.arg; }
  virtual bool indirect () const { const Memory & m = *this; return m.indirect; }

  virtual void execute (Thread & t) const { t.execute(pod); }
  virtual string encode (Encoder & e) const { return e.encode(pod); }

  virtual operator const Unary & () const
    {
      assert(is_unary());
      return dynamic_cast<const Unary &>(pod);
    }

  virtual operator const Memory & () const
    {
      assert(is_memory());
      return dynamic_cast<const Memory &>(pod);
    }
};

//==============================================================================
// Instruction
//==============================================================================

//------------------------------------------------------------------------------
// constructors
//------------------------------------------------------------------------------

template <class T>
Instruction::Instruction (const T & pod) :
  model(make_unique<Model<T>>(pod))
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

const string & Instruction::symbol () const { return model->symbol(); }

uint8_t Instruction::type () const { return model->type(); }
void Instruction::type (uint8_t t) { model->type(t); }

word_t Instruction::arg () const { return model->arg(); }
bool Instruction::indirect () const { return model->indirect(); }

void Instruction::execute (Thread & t) const { model->execute(t); }
string Instruction::encode (Encoder & e) const { return model->encode(e); }

//------------------------------------------------------------------------------
// member operators
//------------------------------------------------------------------------------

// assignment ------------------------------------------------------------------

Instruction & Instruction::operator = (const Instruction & other)
{
  model = other.model->clone();
  return *this;
}

// conversion ------------------------------------------------------------------

Instruction::operator const Unary & () const { return *model; }
Instruction::operator const Memory & () const { return *model; }

//==============================================================================
// non-member operators
//==============================================================================

// equality --------------------------------------------------------------------

bool operator == (const Instruction & a, const Instruction & b)
{
  if (a.symbol() != b.symbol())
    return false;

  if (a.type() != b.type())
    return false;

  if (a.is_memory() && b.is_memory())
    {
      const Instruction::Memory & ma = a, mb = b;

      return ma.arg == mb.arg && ma.indirect == mb.indirect;
    }
  else if (a.is_unary() && b.is_unary())
    {
      const Instruction::Unary & ua = a, ub = b;

      return ua.arg == ub.arg;
    }

  return true;
}

bool operator != (const Instruction & a, const Instruction & b)
{
  return !(a == b);
}
