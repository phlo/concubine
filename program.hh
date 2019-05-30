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
  Program (std::istream & file, std::string & name);

  /* path to program file */
  std::string                     path;

  /* checkpoint ids */
  std::unordered_set<word_t>      check_ids;

  /* maps program counters to the label referencing it */
  std::unordered_map<
    word_t,
    const std::string *>          pc_to_label;

  /* maps labels to the corresponding program counter */
  std::unordered_map<
    const std::string *,
    word_t>                       label_to_pc;

  /* jump labels */
  std::unordered_set<std::string> labels;

  /* appends instruction to the program */
  void                            push_back (Instruction_ptr);

  /* get pc corresponding to the given label */
  word_t                          get_pc (const std::string label) const;

  /* get label corresponding to the given pc */
  std::string                     get_label (const word_t) const;

  /* print whole program */
  std::string                     print (bool) const;

  /* print instruction at pc */
  std::string                     print (bool, word_t) const;
};

/*******************************************************************************
 * Operators
 ******************************************************************************/
bool operator == (const Program &, const Program &);
bool operator != (const Program &, const Program &);

/*******************************************************************************
 * Program_ptr
 ******************************************************************************/
using Program_ptr = std::shared_ptr<Program>;

/*******************************************************************************
 * Program_list
 ******************************************************************************/
using Program_list = std::deque<Program_ptr>;

/*******************************************************************************
 * Program_list_ptr
 ******************************************************************************/
using Program_list_ptr = std::shared_ptr<Program_list>;

#endif
