#ifndef INSTRUCTIONSET_HH_
#define INSTRUCTIONSET_HH_

#include <string>
#include <unordered_map>

#include "common.hh"

using namespace std;

/* forward declerations */
struct Thread;

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
   // NOTE: really neccessary?
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
      Jz,
      Jnz,
      Jl,
      Jle,
      Jg,
      Jge,
      Mem,
      Cas
    };

/* Instruction Set - containing object factories to simplify parsing **********/
  struct Set
    {
      /* map containing pointers to instruction object factories */
      static  unordered_map<string, Instruction * (*)()>
              nullaryFactory;

      /* map containing pointers to unary instruction object factories */
      static  unordered_map<string, Instruction * (*)(const word)>
              unaryFactory;

      virtual ~Set (void) = 0; // for a purely static class

      static Instruction::Type        contains (string &);
      static shared_ptr<Instruction>  create (string &);
      static shared_ptr<Instruction>  create (string &, const word);
    };

  /* Instruction Members */
  virtual Type            getType   (void);
  virtual OPCode          getOPCode (void) = 0;
  virtual const string &  getSymbol (void) = 0;

  virtual void            execute (Thread &) = 0;

  virtual void            print (Thread &);
};

typedef shared_ptr<Instruction> InstructionPtr;


/*******************************************************************************
 * Unary Instruction Base Class
 ******************************************************************************/
struct UnaryInstruction : public Instruction
{
  const word      arg;

  UnaryInstruction (const word);

  virtual Type    getType (void);

  virtual void    execute (Thread &) = 0;

  virtual void    print (Thread &);
};

typedef shared_ptr<UnaryInstruction> UnaryInstructionPtr;


/*******************************************************************************
 * Instructions
 ******************************************************************************/
#define DECLARE_COMMON_INSTRUCTION_MEMBERS()      \
    static  const string      symbol;             \
                                                  \
    virtual       OPCode      getOPCode ();       \
    virtual const string&     getSymbol ();       \
                                                  \
    virtual       void        execute (Thread &);

#define DECLARE_INSTRUCTION_NULLARY(classname)  \
  class classname : public Instruction          \
  {                                             \
    DECLARE_COMMON_INSTRUCTION_MEMBERS ()       \
  };

#define DECLARE_INSTRUCTION_UNARY(classname)  \
  class classname : public UnaryInstruction   \
  {                                           \
    DECLARE_COMMON_INSTRUCTION_MEMBERS ()     \
    classname (const word);                   \
  };

DECLARE_INSTRUCTION_UNARY   (Sync)
DECLARE_INSTRUCTION_NULLARY (Halt)
DECLARE_INSTRUCTION_UNARY   (Exit)

DECLARE_INSTRUCTION_UNARY   (Load)
DECLARE_INSTRUCTION_UNARY   (Store)

DECLARE_INSTRUCTION_UNARY   (Add)
DECLARE_INSTRUCTION_UNARY   (Addi)
DECLARE_INSTRUCTION_UNARY   (Sub)
DECLARE_INSTRUCTION_UNARY   (Subi)

DECLARE_INSTRUCTION_UNARY   (Cmp)
DECLARE_INSTRUCTION_UNARY   (Jz)
DECLARE_INSTRUCTION_UNARY   (Jnz)
DECLARE_INSTRUCTION_UNARY   (Jl)
DECLARE_INSTRUCTION_UNARY   (Jle)
DECLARE_INSTRUCTION_UNARY   (Jg)
DECLARE_INSTRUCTION_UNARY   (Jge)

DECLARE_INSTRUCTION_NULLARY (Mem)
DECLARE_INSTRUCTION_UNARY   (Cas)
#endif
