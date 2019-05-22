#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <deque>
#include <istream>
#include <memory>
#include <unordered_map>
#include <unordered_set>

#include "common.hh"

struct Instruction;
using Instruction_ptr = std::shared_ptr<Instruction>;

/*******************************************************************************
 * Program
 ******************************************************************************/
struct Program : public std::deque<Instruction_ptr>
{
  /* default constructor (for testing) */
  Program (void);

  /* construct from file */
  Program (std::istream &, std::string &);

  /* path to program file */
  std::string                     path;

  /* checkpoint ids */
  std::unordered_set<word>        check_ids;

  /* maps program counters to the label referencing it */
  std::unordered_map<
    word,
    const std::string *>          pc_to_label;

  /* maps labels to the corresponding program counter */
  std::unordered_map<
    const std::string *,
    word>                         label_to_pc;

  /* jump labels */
  std::unordered_set<std::string> labels;

  /* appends instruction to the program */
  void                            push_back (Instruction_ptr);

  /* get pc corresponding to the given label */
  word                            get_pc (const std::string label) const;

  /* get label corresponding to the given pc */
  std::string                     get_label (const word) const;

  /* print whole program */
  std::string                     print (bool) const;

  /* print instruction at pc */
  std::string                     print (bool, word) const;
};

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Program &, const Program &);
bool operator != (const Program &, const Program &);

/*******************************************************************************
 * ProgramPtr
 ******************************************************************************/
typedef std::shared_ptr<Program> ProgramPtr;

/*******************************************************************************
 * ProgramList
 ******************************************************************************/
typedef std::deque<ProgramPtr> ProgramList;

/*******************************************************************************
 * ProgramListPtr
 ******************************************************************************/
typedef std::shared_ptr<ProgramList> ProgramListPtr;

#endif
