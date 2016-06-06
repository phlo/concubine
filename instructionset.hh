#ifndef INSTRUCTIONSET_HH_
#define INSTRUCTIONSET_HH_

#include <string>
#include <unordered_map>

#include "common.hh"

using namespace std;

/* forward declarations */
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

#define DECLARE_INSTRUCTION_NULLARY(classname, baseclass) \
  struct classname : public baseclass                     \
  {                                                       \
    DECLARE_COMMON_INSTRUCTION_MEMBERS ()                 \
  };

#define DECLARE_INSTRUCTION_UNARY(classname, baseclass) \
  struct classname : public baseclass                   \
  {                                                     \
    DECLARE_COMMON_INSTRUCTION_MEMBERS ()               \
    classname (const word a) : baseclass(a) {};         \
  };

DECLARE_INSTRUCTION_UNARY   (Sync,  UnaryInstruction)
DECLARE_INSTRUCTION_UNARY   (Exit,  UnaryInstruction)

DECLARE_INSTRUCTION_UNARY   (Load,  UnaryInstruction)
DECLARE_INSTRUCTION_UNARY   (Store, UnaryInstruction)

DECLARE_INSTRUCTION_UNARY   (Add,   Load)
DECLARE_INSTRUCTION_UNARY   (Addi,  UnaryInstruction)
DECLARE_INSTRUCTION_UNARY   (Sub,   Load)
DECLARE_INSTRUCTION_UNARY   (Subi,  UnaryInstruction)

DECLARE_INSTRUCTION_UNARY   (Cmp,   Load)
DECLARE_INSTRUCTION_UNARY   (Jmp,   UnaryInstruction)
DECLARE_INSTRUCTION_UNARY   (Jz,    Jmp)
DECLARE_INSTRUCTION_UNARY   (Jnz,   Jmp)
#ifdef MACHINE_TYPE_SIGNED
DECLARE_INSTRUCTION_UNARY   (Jl,    Jmp)
DECLARE_INSTRUCTION_UNARY   (Jle,   Jmp)
DECLARE_INSTRUCTION_UNARY   (Jg,    Jmp)
DECLARE_INSTRUCTION_UNARY   (Jge,   Jmp)
#endif

DECLARE_INSTRUCTION_UNARY   (Mem,   Load)
DECLARE_INSTRUCTION_UNARY   (Cas,   Load)
#endif
