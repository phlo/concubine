#ifndef INSTRUCTION_HH_
#define INSTRUCTION_HH_

#include <functional>
#include <memory>
#include <string>
#include <unordered_map>

#include "common.hh"

//==============================================================================
// macros
//==============================================================================

// simplify declaration of instruction PODs ------------------------------------
//
#define DECLARE_NULLARY(classname, baseclass, _symbol, _type) \
  struct classname : baseclass \
  { \
    inline static const std::string & symbol = \
      add_nullary<classname>(_symbol, _type); \
  }; \

#define DECLARE_UNARY(classname, baseclass, _symbol, _type) \
  struct classname : baseclass \
  { \
    inline static const std::string & symbol = \
      add_unary<classname>(_symbol, _type); \
  }; \

#define DECLARE_MEMORY(classname, baseclass, _symbol, _type) \
  struct classname : baseclass \
  { \
    inline static const std::string & symbol = \
      add_memory<classname>(_symbol, _type); \
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
  // static members
  //----------------------------------------------------------------------------

  // map containing pointers to nullary instruction object factories
  //
  using nullary_factory_map =
    std::unordered_map<
      std::string,
      std::function<Instruction()>>;

  static std::unique_ptr<nullary_factory_map> nullary_factory;

  // map containing pointers to unary instruction object factories
  //
  using unary_factory_map =
    std::unordered_map<
      std::string,
      std::function<Instruction(word_t)>>;

  static std::unique_ptr<unary_factory_map> unary_factory;

  // map containing pointers to memory instruction object factories
  //
  using memory_factory_map =
    std::unordered_map<
      std::string,
      std::function<Instruction(word_t, bool)>>;

  static std::unique_ptr<memory_factory_map> memory_factory;

  //----------------------------------------------------------------------------
  // static member functions
  //----------------------------------------------------------------------------

  static bool contains (const std::string & symbol);

  template <class POD>
  static const std::string & add_nullary (const std::string & symbol,
                                          uint8_t type);
  template <class POD>
  static const std::string & add_unary (const std::string & symbol,
                                        uint8_t type);
  template <class POD>
  static const std::string & add_memory (const std::string & symbol,
                                         uint8_t type);

  // copy elision
  //
  static Instruction create (const std::string & symbol);
  static Instruction create (const std::string & symbol, word_t arg);
  static Instruction create (const std::string & symbol,
                             word_t arg,
                             bool indirect);

  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  // instruction types ---------------------------------------------------------
  //
  enum Type : uint8_t
    {
      none    = 0,
      accu    = 1 << 0,     // modifies accu
      mem     = 1 << 1,     // modifies mem
      modify  = accu | mem, // modifies a register
      read    = 1 << 2,     // reads from memory
      write   = 1 << 3,     // writes to memory
      atomic  = 1 << 4,     // atomic instruction
      barrier = 1 << 5,     // memory barrier
      control = 1 << 6      // control flow
    };

  // instruction PODs ----------------------------------------------------------
  //
  struct Nullary { uint8_t type = Type::none; };
  struct Unary : Nullary { word_t arg = 0; };
  struct Memory : Unary { bool indirect = false; };

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
  DECLARE_UNARY   (Jmp,   Unary,    "JMP",    control)
  DECLARE_UNARY   (Jz,    Jmp,      "JZ",     control)
  DECLARE_UNARY   (Jnz,   Jmp,      "JNZ",    control)
  DECLARE_UNARY   (Js,    Jmp,      "JS",     control)
  DECLARE_UNARY   (Jns,   Jmp,      "JNS",    control)
  DECLARE_UNARY   (Jnzns, Jmp,      "JNZNS",  control)

  DECLARE_MEMORY  (Mem,   Load,     "MEM",    accu | mem | read)
  DECLARE_MEMORY  (Cas,   Store,    "CAS",    accu | read | atomic | barrier)

  DECLARE_UNARY   (Check, Unary,    "CHECK",  control)

  DECLARE_NULLARY (Halt,  Nullary,  "HALT",   control)
  DECLARE_UNARY   (Exit,  Unary,    "EXIT",   control)

  // abstract interface (types erasure concept) --------------------------------
  //
  struct Concept
    {
      virtual std::unique_ptr<Concept> clone () const = 0;

      virtual bool is_nullary () const = 0;
      virtual bool is_unary () const = 0;
      virtual bool is_memory () const = 0;
      virtual bool is_jump () const = 0;

      virtual bool requires_flush () const = 0;

      virtual const std::string & symbol () const = 0;

      virtual uint8_t type () const = 0;
      virtual void type (uint8_t type) = 0;

      virtual word_t arg () const = 0;
      virtual void arg (word_t arg) = 0;

      virtual bool indirect () const = 0;
      virtual void indirect (bool indirect) = 0;

      virtual void execute (Thread & t) const = 0;
      virtual std::string encode (Encoder & e) const = 0;
    };

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  std::unique_ptr<Concept> model;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  Instruction () = default;

  // construct embedding a given POD
  //
  template <class POD>
  Instruction (const POD & pod);

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
  void arg (word_t arg);

  bool indirect () const;
  void indirect (bool indirect);

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
};

//==============================================================================
// non-member operators
//==============================================================================

// equality
//
bool operator == (const Instruction &, const Instruction &);
bool operator != (const Instruction &, const Instruction &);

#endif
