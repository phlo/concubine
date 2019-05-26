#ifndef INSTRUCTIONSET_HH_
#define INSTRUCTIONSET_HH_

#include <memory>
#include <string>
#include <unordered_map>

#include "common.hh"

/* forward declarations */
struct Thread;
struct Encoder;

/*******************************************************************************
 * Common Instruction Base Class (Nullary)
 ******************************************************************************/
struct Instruction
{
  /* Instruction Types */
  using Type = uint8_t;

  enum Types : Type
    {
      none    = 0,
      accu    = 1 << 1, // modifies accu
      mem     = 1 << 2, // modifies mem
      read    = 1 << 3, // reads from memory
      write   = 1 << 4, // writes to memory
      barrier = 1 << 5, // memory barrier
      atomic  = 1 << 6 | barrier // atomic instruction
    };

  /* Instruction Set - containing object factories to simplify parsing ********/
  struct Set
    {
      /* map containing pointers to instruction object factories */
      static
      std::unordered_map<std::string, Instruction * (*)()>
      nullary_factory;

      /* map containing pointers to unary instruction object factories */
      static
      std::unordered_map<std::string, Instruction * (*)(const word)>
      unary_factory;

      /* map containing pointers to memory instruction object factories */
      static
      std::unordered_map<std::string, Instruction * (*)(const word, const bool)>
      memory_factory;

      virtual ~Set (void) = 0; // for a purely static class

      // NOTE: really needed?
      static bool contains (std::string);

      typedef std::shared_ptr<Instruction> Instruction_ptr; // readability

      static Instruction_ptr create (const std::string & name);
      static Instruction_ptr create (const std::string & name, const word arg);
      static Instruction_ptr create (
                                     const std::string & name,
                                     const word arg,
                                     const bool indirect
                                    );
    };

  /* Instruction Members ******************************************************/
  virtual const std::string & symbol (void) const = 0;
  virtual Type                type   (void) const = 0;

  virtual void                execute (Thread &) = 0;
  virtual std::string         encode (Encoder &) = 0;
};

using Instruction_ptr = std::shared_ptr<Instruction>;

/*******************************************************************************
 * Unary Instruction Base Class
 ******************************************************************************/
struct Unary : public Instruction
{
  const word arg;

  Unary (const word);
};

using Unary_ptr = std::shared_ptr<Unary>;

/*******************************************************************************
 * Memory Access Instruction Base Class
 ******************************************************************************/
struct Memory : public Unary
{
  bool indirect;

  Memory (const word, const bool = false);
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
#define DECLARE_MEMBERS \
    static  const std::string   _symbol; \
    static  const Type          _type; \
    \
    virtual const std::string & symbol () const; \
    virtual       Type          type () const; \
    \
    virtual       void          execute (Thread &); \
    virtual       std::string   encode (Encoder &);

#define DECLARE_NULLARY(classname, baseclass) \
  struct classname : baseclass \
  { \
    DECLARE_MEMBERS \
  }; \
  using classname##_ptr = std::shared_ptr<classname>;

#define DECLARE_UNARY(classname, baseclass) \
  struct classname : baseclass \
  { \
    DECLARE_MEMBERS \
    classname (const word a) : baseclass(a) {}; \
  }; \
  using classname##_ptr = std::shared_ptr<classname>;

#define DECLARE_MEMORY(classname, baseclass) \
  struct classname : baseclass \
  { \
    DECLARE_MEMBERS \
    classname (const word a, const bool i = false) : baseclass(a, i) {}; \
  }; \
  using classname##_ptr = std::shared_ptr<classname>;

DECLARE_MEMORY  (Load,  Memory)
DECLARE_MEMORY  (Store, Memory)

DECLARE_NULLARY (Fence, Instruction)

DECLARE_MEMORY  (Add,   Load)
DECLARE_UNARY   (Addi,  Unary)
DECLARE_MEMORY  (Sub,   Load)
DECLARE_UNARY   (Subi,  Unary)

DECLARE_MEMORY  (Cmp,   Load)
DECLARE_UNARY   (Jmp,   Unary)
DECLARE_UNARY   (Jz,    Jmp)
DECLARE_UNARY   (Jnz,   Jmp)
DECLARE_UNARY   (Js,    Jmp)
DECLARE_UNARY   (Jns,   Jmp)
DECLARE_UNARY   (Jnzns, Jmp)

DECLARE_MEMORY  (Mem,   Load)
DECLARE_MEMORY  (Cas,   Store)

DECLARE_UNARY   (Check, Unary)
DECLARE_NULLARY (Halt,  Instruction)
DECLARE_UNARY   (Exit,  Unary)
#endif
