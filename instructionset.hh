#ifndef INSTRUCTIONSET_HH_
#define INSTRUCTIONSET_HH_

#include <memory>
#include <string>
#include <unordered_map>

#include "common.hh"

// forward declarations
struct Thread;
struct Encoder;

/*******************************************************************************
 * Common Instruction Base Class (Nullary)
 ******************************************************************************/
struct Instruction
{
  // Instruction Set - containing object factories to simplify parsing
  struct Set
    {
      // map containing pointers to instruction object factories
      static
      std::unique_ptr<std::unordered_map<
        std::string,
        Instruction * (*)()>> nullary_factory;

      // map containing pointers to unary instruction object factories
      static
      std::unique_ptr<std::unordered_map<
        std::string,
        Instruction * (*)(const word_t)>> unary_factory;

      // map containing pointers to memory instruction object factories
      static
      std::unique_ptr<std::unordered_map<
        std::string,
        Instruction * (*)(const word_t, const bool)>> memory_factory;

      virtual ~Set () = 0; // for a purely static class

      // NOTE: really needed?
      static bool contains (std::string);

      // template <typename T, typename E>
      // static std::string add (std::string symbol);

      template <class T>
      static std::string add_nullary (std::string symbol);
      template <class T>
      static std::string add_unary (std::string symbol);
      template <class T>
      static std::string add_memory (std::string symbol);

      using Instruction_ptr = std::shared_ptr<Instruction>; // readability

      static Instruction_ptr create (const std::string & name);
      static Instruction_ptr create (
                                     const std::string & name,
                                     const word_t arg
                                    );
      static Instruction_ptr create (
                                     const std::string & name,
                                     const word_t arg,
                                     const bool indirect
                                    );
    };

  // Instruction Types
  using Type = uint8_t;

  enum Types : Type
    {
      none    = 0,
      accu    = 1 << 0, // modifies accu
      mem     = 1 << 1, // modifies mem
      modify  = accu | mem, // modifies a register
      read    = 1 << 2, // reads from memory
      write   = 1 << 3, // writes to memory
      atomic  = 1 << 4, // atomic instruction
      barrier = 1 << 5, // memory barrier
      control = 1 << 6  // control flow
    };

  Type type;

  Instruction (Type type);

  /* Instruction Members ******************************************************/
  bool                        requires_flush ();

  virtual const std::string & symbol (void) const = 0;
  virtual void                execute (Thread &) = 0;
  virtual std::string         encode (Encoder &) = 0;
};

using Instruction_ptr = std::shared_ptr<Instruction>;

/*******************************************************************************
 * Unary Instruction Base Class
 ******************************************************************************/
struct Unary : public Instruction
{
  const word_t arg;

  Unary (Type type, word_t arg);
};

using Unary_ptr = std::shared_ptr<Unary>;

/*******************************************************************************
 * Memory Access Instruction Base Class
 ******************************************************************************/
struct Memory : public Unary
{
  const bool indirect;

  Memory (Type type, word_t arg, bool indirect = false);
};

using Memory_ptr = std::shared_ptr<Memory>;

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Instruction &, const Instruction &);
bool operator != (const Instruction &, const Instruction &);

/*******************************************************************************
 * Instructions
 ******************************************************************************/
#define DECLARE_MEMBERS(classname, sym) \
    virtual const std::string & symbol () const; \
    virtual       void          execute (Thread &); \
    virtual       std::string   encode (Encoder &);

#define DECLARE_NULLARY(classname, baseclass, symbol, type) \
  struct classname : baseclass \
  { \
    inline static const std::string _symbol = Set::add_nullary<classname>(symbol); \
    \
    DECLARE_MEMBERS(classname, symbol) \
    classname () : baseclass(type) {}; \
    classname (Type t) : baseclass(t) {}; \
  }; \
  using classname##_ptr = std::shared_ptr<classname>;

#define DECLARE_UNARY(classname, baseclass, symbol, type) \
  struct classname : baseclass \
  { \
    inline static const std::string _symbol = Set::add_unary<classname>(symbol); \
    \
    DECLARE_MEMBERS(classname, symbol) \
    classname (const word_t a) : baseclass(type, a) {}; \
    classname (Type t, word_t a) : baseclass(t, a) {}; \
  }; \
  using classname##_ptr = std::shared_ptr<classname>;

#define DECLARE_MEMORY(classname, baseclass, symbol, type) \
  struct classname : baseclass \
  { \
    inline static const std::string _symbol = Set::add_memory<classname>(symbol); \
    \
    DECLARE_MEMBERS(classname, symbol) \
    classname (word_t a, bool i = false) : baseclass(type, a, i) {}; \
    classname (Type t, word_t a, bool i = false) : baseclass(t, a, i) {}; \
  }; \
  using classname##_ptr = std::shared_ptr<classname>;

DECLARE_MEMORY  (Load,  Memory,       "LOAD",   accu | read)
DECLARE_MEMORY  (Store, Memory,       "STORE",  write)

DECLARE_NULLARY (Fence, Instruction,  "FENCE",  barrier)

DECLARE_MEMORY  (Add,   Load,         "ADD",    accu | read)
DECLARE_UNARY   (Addi,  Unary,        "ADDI",   accu)
DECLARE_MEMORY  (Sub,   Load,         "SUB",    accu | read)
DECLARE_UNARY   (Subi,  Unary,        "SUBI",   accu)
DECLARE_MEMORY  (Mul,   Load,         "MUL",    accu | read)
DECLARE_UNARY   (Muli,  Unary,        "MULI",   accu)

DECLARE_MEMORY  (Cmp,   Load,         "CMP",    accu | read)
DECLARE_UNARY   (Jmp,   Unary,        "JMP",    control)
DECLARE_UNARY   (Jz,    Jmp,          "JZ",     control)
DECLARE_UNARY   (Jnz,   Jmp,          "JNZ",    control)
DECLARE_UNARY   (Js,    Jmp,          "JS",     control)
DECLARE_UNARY   (Jns,   Jmp,          "JNS",    control)
DECLARE_UNARY   (Jnzns, Jmp,          "JNZNS",  control)

DECLARE_MEMORY  (Mem,   Load,         "MEM",    accu | mem | read)
DECLARE_MEMORY  (Cas,   Store,        "CAS",    accu | read | atomic | barrier)

DECLARE_UNARY   (Check, Unary,        "CHECK",  control)

DECLARE_NULLARY (Halt,  Instruction,  "HALT",   control)
DECLARE_UNARY   (Exit,  Unary,        "EXIT",   control)
#endif
