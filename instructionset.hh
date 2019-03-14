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
  enum Type
    {
      UNKNOWN = 0,
      NULLARY,
      UNARY,
      MEMORY
    };

   /* OP Codes */
   // NOTE: really necessary?
  enum OPCode
    {
      Exit,
      Halt,
      Sync,
      Load,
      Store,
      Add,
      Addi,
      Sub,
      Subi,
      Cmp,
      Jmp,
      Jz,
      Jnz,
      Js,
      Jns,
      Jnzns,
      Mem,
      Cas
    };

  /* Instruction Attributes */
  struct Attributes
    {
      static const unsigned char ALTERS_HEAP;
      static const unsigned char ALTERS_ACCU;
      static const unsigned char ALTERS_MEM;
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

      static Instruction::Type  contains (std::string);

      typedef std::shared_ptr<Instruction> InstructionPtr; // readability

      static InstructionPtr create (std::string);
      static InstructionPtr create (std::string, const word);
      static InstructionPtr create (std::string, const word, const bool);
    };

  /* Instruction Members ******************************************************/
  virtual Type                get_type   (void) const;
  virtual OPCode              get_opcode (void) const = 0;
  virtual const std::string & get_symbol (void) const = 0;
  virtual unsigned char       get_attributes (void) const = 0;

  virtual void                execute (Thread &) = 0;

  virtual std::string         encode (Encoder &) = 0;
};

typedef std::shared_ptr<Instruction> InstructionPtr;

/*******************************************************************************
 * Unary Instruction Base Class
 ******************************************************************************/
struct UnaryInstruction : public Instruction
{
  const word arg;

  UnaryInstruction (const word);

  virtual Type          get_type (void) const;
  virtual unsigned char get_attributes (void) const = 0;

  virtual void          execute (Thread &) = 0;

  virtual std::string   encode (Encoder &) = 0;
};

typedef std::shared_ptr<UnaryInstruction> UnaryInstructionPtr;

/*******************************************************************************
 * Memory Access Instruction Base Class (for indirect addressing)
 ******************************************************************************/
struct MemoryInstruction : public UnaryInstruction
{
  bool indirect;

  MemoryInstruction (const word, const bool = false);

  virtual Type          get_type (void) const;
  virtual unsigned char get_attributes (void) const = 0;

  virtual void          execute (Thread &) = 0;

  virtual std::string   encode (Encoder &) = 0;
};

typedef std::shared_ptr<MemoryInstruction> MemoryInstructionPtr;

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Instruction &, const Instruction &);
bool operator != (const Instruction &, const Instruction &);

/*******************************************************************************
 * Instructions
 ******************************************************************************/
#define DECLARE_COMMON_INSTRUCTION_MEMBERS()                  \
    static  const std::string   symbol;                       \
    static  const unsigned char attributes;                   \
                                                              \
    virtual       OPCode        get_opcode () const;          \
    virtual const std::string & get_symbol () const;          \
    virtual       unsigned char get_attributes (void) const;  \
                                                              \
    virtual       void          execute (Thread &);           \
                                                              \
    virtual       std::string   encode (Encoder &);           \

#define DECLARE_INSTRUCTION_NULLARY(classname, baseclass, ...)  \
  struct classname : public baseclass                           \
  {                                                             \
    DECLARE_COMMON_INSTRUCTION_MEMBERS ()                       \
    __VA_ARGS__                                                 \
  };                                                            \
  typedef std::shared_ptr<classname> classname##Ptr;

#define DECLARE_INSTRUCTION_UNARY(classname, baseclass, ...)  \
  struct classname : public baseclass                         \
  {                                                           \
    DECLARE_COMMON_INSTRUCTION_MEMBERS ()                     \
    __VA_ARGS__                                               \
    classname (const word a) : baseclass(a) {};               \
  };                                                          \
  typedef std::shared_ptr<classname> classname##Ptr;

#define DECLARE_INSTRUCTION_MEMORY(classname, baseclass, ...)             \
  struct classname : public baseclass                                     \
  {                                                                       \
    DECLARE_COMMON_INSTRUCTION_MEMBERS ()                                 \
    __VA_ARGS__                                                           \
    classname (const word a, const bool i = false) : baseclass(a, i) {};  \
  };                                                                      \
  typedef std::shared_ptr<classname> classname##Ptr;

DECLARE_INSTRUCTION_MEMORY  (Load,  MemoryInstruction, )
DECLARE_INSTRUCTION_MEMORY  (Store, MemoryInstruction, )

DECLARE_INSTRUCTION_MEMORY  (Add,   Load, )
DECLARE_INSTRUCTION_UNARY   (Addi,  UnaryInstruction, )
DECLARE_INSTRUCTION_MEMORY  (Sub,   Load, )
DECLARE_INSTRUCTION_UNARY   (Subi,  UnaryInstruction, )

DECLARE_INSTRUCTION_MEMORY  (Cmp,   Load, )
DECLARE_INSTRUCTION_UNARY   (Jmp,   UnaryInstruction, )
DECLARE_INSTRUCTION_UNARY   (Jz,    Jmp, )
DECLARE_INSTRUCTION_UNARY   (Jnz,   Jmp, )
DECLARE_INSTRUCTION_UNARY   (Js,    Jmp, )
DECLARE_INSTRUCTION_UNARY   (Jns,   Jmp, )
DECLARE_INSTRUCTION_UNARY   (Jnzns, Jmp, )

DECLARE_INSTRUCTION_MEMORY  (Mem,   Load, )
DECLARE_INSTRUCTION_MEMORY  (Cas,   Store, )

DECLARE_INSTRUCTION_UNARY   (Sync,  UnaryInstruction, )
DECLARE_INSTRUCTION_UNARY   (Exit,  UnaryInstruction, )
#endif
