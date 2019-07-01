#ifndef INSTRUCTION_HH_
#define INSTRUCTION_HH_

#include <memory>
#include <string>
#include <unordered_map>

#include "common.hh"

//==============================================================================
// macros
//==============================================================================

// simplify declaration of instruction PODs ------------------------------------

#define DECLARE_NULLARY(classname, baseclass, _symbol, _type) \
  struct classname : public baseclass \
  { \
    inline static const std::string & symbol = \
      Set::add_nullary<classname>(_symbol); \
    \
    classname () : baseclass(_type) {} \
    classname (uint8_t t) : baseclass(t) {} \
  }; \

#define DECLARE_UNARY(classname, baseclass, _symbol, _type) \
  struct classname : public baseclass \
  { \
    inline static const std::string & symbol = \
      Set::add_unary<classname>(_symbol); \
    \
    classname (word_t a) : baseclass(_type, a) {} \
    classname (uint8_t t, word_t a) : baseclass(t, a) {} \
  }; \

#define DECLARE_MEMORY(classname, baseclass, _symbol, _type) \
  struct classname : public baseclass \
  { \
    inline static const std::string & symbol = \
      Set::add_memory<classname>(_symbol); \
    \
    classname (word_t a, bool i = false) : baseclass(_type, a, i) {} \
    classname (uint8_t t, word_t a, bool i = false) : baseclass(t, a, i) {} \
  }; \

//==============================================================================
// forward declarations
//==============================================================================

struct Thread;
struct Encoder;

//==============================================================================
// Instruction class
//
// * type erasure on PODs
//==============================================================================

struct Instruction
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  // object factories to simplify parsing --------------------------------------

  struct Set
    {
      virtual ~Set () = 0; // for a purely static class

      //------------------------------------------------------------------------
      // static members
      //------------------------------------------------------------------------

      // map containing pointers to nullary instruction object factories
      //
      using nullary_t =
          std::unordered_map<
            std::string,
            Instruction (*) ()>;

      static std::unique_ptr<nullary_t> nullary;

      // map containing pointers to unary instruction object factories
      //
      using unary_t =
        std::unordered_map<
          std::string,
          Instruction (*) (word_t)>;

      static std::unique_ptr<unary_t> unary;

      // map containing pointers to memory instruction object factories
      //
      using memory_t =
        std::unordered_map<
          std::string,
          Instruction (*) (word_t, bool)>;

      static std::unique_ptr<memory_t> memory;

      //------------------------------------------------------------------------
      // static member functions
      //------------------------------------------------------------------------

      // NOTE: really needed?
      static bool contains (const std::string & symbol);

      template <class POD>
      static const std::string & add_nullary (const std::string && symbol);
      template <class POD>
      static const std::string & add_unary (const std::string && symbol);
      template <class POD>
      static const std::string & add_memory (const std::string && symbol);

      // copy elision
      //
      static Instruction create (const std::string & symbol);
      static Instruction create (const std::string & symbol, const word_t arg);
      static Instruction create (const std::string & symbol,
                                 const word_t arg,
                                 const bool indirect);
    };

  // instruction types ---------------------------------------------------------

  enum Type : uint8_t
    {
      none    = 0,
      accu    = 1 << 0, // modifies accu
      mem     = 1 << 1, // modifies mem
      modify  = accu | mem, // modifies a register
      read    = 1 << 2, // reads from memory
      write   = 1 << 3, // writes to memory
      atomic  = 1 << 4, // atomic instruction
      barrier = 1 << 5, // memory barrier
      control = 1 << 6, // control flow
      jump    = 1 << 7  // jump instruction
    };

  // abstract base classes for instruction PODs --------------------------------

  struct Nullary
    {
      uint8_t type;

      Nullary (uint8_t t) : type(t) {}

      virtual ~Nullary () = default; // some virtual required by dynamic_cast
    };

  struct Unary : public Nullary
    {
      const word_t arg;

      Unary (uint8_t t, word_t a) : Nullary(t), arg(a) {}
    };

  struct Memory : public Unary
    {
      const bool indirect;

      Memory (uint8_t t, word_t a, bool i) : Unary(t, a), indirect(i) {}
    };

  // concrete instruction PODs -------------------------------------------------

  DECLARE_MEMORY  (Load,  Memory,   "LOAD",   accu | read)
  DECLARE_MEMORY  (Store, Memory,   "STORE",  write)

  DECLARE_NULLARY (Fence, Nullary,  "FENCE",  barrier)

  DECLARE_MEMORY  (Add,   Load,     "ADD",    accu | read)
  DECLARE_UNARY   (Addi,  Unary,    "ADDI",   accu)
  DECLARE_MEMORY  (Sub,   Load,     "SUB",    accu | read)
  DECLARE_UNARY   (Subi,  Unary,    "SUBI",   accu)
  DECLARE_MEMORY  (Mul,   Load,     "MUL",    accu | read)
  DECLARE_UNARY   (Muli,  Unary,    "MULI",   accu)

  DECLARE_MEMORY  (Cmp,   Load,     "CMP",    accu | read)
  DECLARE_UNARY   (Jmp,   Unary,    "JMP",    control | jump)
  DECLARE_UNARY   (Jz,    Jmp,      "JZ",     control | jump)
  DECLARE_UNARY   (Jnz,   Jmp,      "JNZ",    control | jump)
  DECLARE_UNARY   (Js,    Jmp,      "JS",     control | jump)
  DECLARE_UNARY   (Jns,   Jmp,      "JNS",    control | jump)
  DECLARE_UNARY   (Jnzns, Jmp,      "JNZNS",  control | jump)

  DECLARE_MEMORY  (Mem,   Load,     "MEM",    accu | mem | read)
  DECLARE_MEMORY  (Cas,   Store,    "CAS",    accu | read | atomic | barrier)

  DECLARE_UNARY   (Check, Unary,    "CHECK",  control)

  DECLARE_NULLARY (Halt,  Nullary,  "HALT",   control)
  DECLARE_UNARY   (Exit,  Unary,    "EXIT",   control)

  // abstract interface (types erasure concept) --------------------------------

  struct Concept
    {
      using pointer = std::unique_ptr<Concept>;

      virtual pointer clone () const = 0;

      virtual bool is_nullary () const = 0;
      virtual bool is_unary () const = 0;
      virtual bool is_memory () const = 0;
      virtual bool is_jump () const = 0;

      virtual bool requires_flush () const = 0;

      virtual const std::string & symbol () const = 0;

      virtual uint8_t type () const = 0;
      virtual void type (uint8_t type) = 0;

      virtual word_t arg () const = 0;
      virtual bool indirect () const = 0;

      virtual void execute (Thread & t) const = 0;
      virtual std::string encode (Encoder & e) const = 0;

      virtual operator const Instruction::Unary & () const = 0;
      virtual operator const Instruction::Memory & () const = 0;
    };

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  Concept::pointer model;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Instruction () = default;

  // construct embedding a given POD
  //
  template <class T>
  Instruction (const T & pod);

  // copy constructor
  //
  // * implicitly deleted due to std::unique_ptr member
  //
  Instruction (const Instruction & other);

  // move constructor
  //
  // * required due to user-declared copy constructor / assignment operator
  //
  Instruction (Instruction && other) = default;

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  bool is_nullary () const;
  bool is_unary () const;
  bool is_memory () const;
  bool is_jump () const;

  bool requires_flush () const;

  const std::string & symbol () const;

  uint8_t type () const;
  void type (uint8_t type);

  word_t arg () const;
  bool indirect () const;

  void execute (Thread & t) const;
  std::string encode (Encoder & e) const;

  //----------------------------------------------------------------------------
  // member operators
  //----------------------------------------------------------------------------

  // copy assignment
  //
  // * implicitly deleted due to std::unique_ptr member
  //
  Instruction & operator = (const Instruction & other);

  // move assignment
  //
  // * required due to user-declared copy constructor / assignment operator
  //
  Instruction & operator = (Instruction && other) = default;

  // conversion into an abstract instruction POD
  //
  operator const Unary & () const;
  operator const Memory & () const;
};

//==============================================================================
// non-member operators
//==============================================================================

// equality
//
bool operator == (const Instruction &, const Instruction &);
bool operator != (const Instruction &, const Instruction &);

#endif
