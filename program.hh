#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <istream>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common.hh"

struct Instruction;
using Instruction_ptr = std::shared_ptr<Instruction>;

/*******************************************************************************
 * Program
 ******************************************************************************/
struct Program : public std::vector<Instruction_ptr>
{
  using Predecessors = std::unordered_map<word_t, std::set<word_t>>;

  /* path to program file */
  std::string                     path;

  /* pc of predecessors for each statement */
  Predecessors                    predecessors;

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

  /* default constructor (testing only) */
  Program ();

  /* construct from file */
  Program (std::istream & file, std::string & path);

  /* appends instruction to the program */
  void                            push_back (Instruction_ptr op);

  /* get pc corresponding to the given label */
  word_t                          get_pc (std::string label) const;

  /* get label corresponding to the given pc */
  std::string                     get_label (word_t pc) const;

  /* print whole program */
  std::string                     print (bool include_pc = false) const;

  /* print instruction at pc */
  std::string                     print (bool include_pc, word_t pc) const;
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
using Program_list = std::vector<Program_ptr>;

/*******************************************************************************
 * Program_list_ptr
 ******************************************************************************/
using Program_list_ptr = std::shared_ptr<Program_list>;

#endif
