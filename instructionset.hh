#ifndef INSTRUCTIONSET_HH_
#define INSTRUCTIONSET_HH_

#include <string>
#include <unordered_map>

using namespace std;

/* forward declerations */
struct Thread;

/*******************************************************************************
 * OPCodes
 * NOTE: really neccessary?
 ******************************************************************************/
enum class OPCode
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

/*******************************************************************************
 * Instruction Base Classes
 ******************************************************************************/
class Instruction
{
public:
  virtual const string& getSymbol () = 0;
  virtual       OPCode  getOPCode () = 0;
  virtual       void    execute (Thread &) = 0;

  virtual void  printDebug (Thread &);
};

class UnaryInstruction : public Instruction
{
protected:
  int           arg;

public:
  virtual void  setArg (int);
  virtual int   getArg (void);

  virtual void  printDebug (Thread &);
};


/*******************************************************************************
 * InstructionSet
 ******************************************************************************/
struct InstructionSet
{
  /* map containing pointers to instruction object factories */
  static unordered_map<string, Instruction * (*)()> factory;
};


/*******************************************************************************
 * Instructions
 ******************************************************************************/
#define DECLARE_INSTRUCTION(classname, baseclass) \
  class classname : public baseclass              \
  {                                               \
    static  const string      symbol;             \
                                                  \
    virtual const string&     getSymbol ();       \
    virtual       OPCode      getOPCode ();       \
                                                  \
    virtual       void        execute (Thread &); \
  };

DECLARE_INSTRUCTION(Exit,   Instruction)
DECLARE_INSTRUCTION(Halt,   Instruction)
DECLARE_INSTRUCTION(Sync,   UnaryInstruction)

DECLARE_INSTRUCTION(Load,   UnaryInstruction)
DECLARE_INSTRUCTION(Store,  UnaryInstruction)

DECLARE_INSTRUCTION(Add,    Load)
DECLARE_INSTRUCTION(Addi,   UnaryInstruction)
DECLARE_INSTRUCTION(Sub,    Load)
DECLARE_INSTRUCTION(Subi,   UnaryInstruction)

DECLARE_INSTRUCTION(Cmp,    Load)
DECLARE_INSTRUCTION(Jz,     UnaryInstruction)
DECLARE_INSTRUCTION(Jnz,    UnaryInstruction)
DECLARE_INSTRUCTION(Jl,     UnaryInstruction)
DECLARE_INSTRUCTION(Jle,    UnaryInstruction)
DECLARE_INSTRUCTION(Jg,     UnaryInstruction)
DECLARE_INSTRUCTION(Jge,    UnaryInstruction)

DECLARE_INSTRUCTION(Mem,    UnaryInstruction)
DECLARE_INSTRUCTION(Cas,    UnaryInstruction)
#endif
