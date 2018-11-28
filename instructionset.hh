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
  /* Instruction Types (Arities) */
  enum Type
    {
      UNKNOWN = 0,
      NULLARY,
      UNARY
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

  /* Instruction Set - containing object factories to simplify parsing ********/
  struct Set
    {
      /* map containing pointers to instruction object factories */
      static  std::unordered_map<std::string, Instruction * (*)()>
              nullaryFactory;

      /* map containing pointers to unary instruction object factories */
      static  std::unordered_map<std::string, Instruction * (*)(const word)>
              unaryFactory;

      virtual ~Set (void) = 0; // for a purely static class

      static Instruction::Type            contains (std::string);
      static std::shared_ptr<Instruction> create (std::string);
      static std::shared_ptr<Instruction> create (std::string, const word);
    };

  /* Instruction Members ******************************************************/
  virtual Type                getType   (void);
  virtual OPCode              getOPCode (void) = 0;
  virtual const std::string & getSymbol (void) = 0;

  virtual void                execute (Thread &) = 0;

  virtual void                encode (Encoder &) = 0;
};

typedef std::shared_ptr<Instruction> InstructionPtr;


/*******************************************************************************
 * Unary Instruction Base Class
 ******************************************************************************/
struct UnaryInstruction : public Instruction
{
  const word      arg;

  UnaryInstruction (const word);

  virtual Type    getType (void);

  virtual void    execute (Thread &) = 0;

  virtual void    encode (Encoder &) = 0;
};

typedef std::shared_ptr<UnaryInstruction> UnaryInstructionPtr;


/*******************************************************************************
 * Memory Access Instruction Base Class (for indirect addressing)
 ******************************************************************************/
struct MemoryInstruction : public UnaryInstruction
{
  bool indirect;

  MemoryInstruction (const word);

  virtual void    execute (Thread &) = 0;

  virtual void    encode (Encoder &) = 0;
};

typedef std::shared_ptr<MemoryInstruction> MemoryInstructionPtr;


/*******************************************************************************
 * Instructions
 ******************************************************************************/
#define DECLARE_COMMON_INSTRUCTION_MEMBERS()                \
    static  const std::string   symbol;                     \
                                                            \
    virtual       OPCode        getOPCode ();               \
    virtual const std::string & getSymbol ();               \
                                                            \
    virtual       void          execute (Thread &);         \
                                                            \
    virtual       void          encode (Encoder &); \

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

DECLARE_INSTRUCTION_UNARY   (Load,  MemoryInstruction, )
DECLARE_INSTRUCTION_UNARY   (Store, MemoryInstruction, )

DECLARE_INSTRUCTION_UNARY   (Add,   Load, )
DECLARE_INSTRUCTION_UNARY   (Addi,  UnaryInstruction, )
DECLARE_INSTRUCTION_UNARY   (Sub,   Load, )
DECLARE_INSTRUCTION_UNARY   (Subi,  UnaryInstruction, )

DECLARE_INSTRUCTION_UNARY   (Cmp,   Load, )
DECLARE_INSTRUCTION_UNARY   (Jmp,   UnaryInstruction, )
DECLARE_INSTRUCTION_UNARY   (Jz,    Jmp, )
DECLARE_INSTRUCTION_UNARY   (Jnz,   Jmp, )
DECLARE_INSTRUCTION_UNARY   (Js,    Jmp, )
DECLARE_INSTRUCTION_UNARY   (Jns,   Jmp, )
DECLARE_INSTRUCTION_UNARY   (Jnzns, Jmp, )

DECLARE_INSTRUCTION_UNARY   (Mem,   Load, )
DECLARE_INSTRUCTION_UNARY   (Cas,   Store, )

DECLARE_INSTRUCTION_UNARY   (Sync,  UnaryInstruction, )
DECLARE_INSTRUCTION_UNARY   (Exit,  UnaryInstruction, )
#endif
