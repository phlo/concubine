#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <istream>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common.hh"

//==============================================================================
// forward declarations
//==============================================================================

struct Instruction;

//==============================================================================
// Program class
//==============================================================================

struct Program : public std::vector<Instruction>
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  struct List : public std::vector<Program>
    {
      using ptr = std::shared_ptr<List>;

      using std::vector<Program>::vector; // inherit constructor
    };

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // path to program file
  //
  std::string path;

  // pc of predecessors for each statement
  //
  std::unordered_map<word_t, std::set<word_t>> predecessors;

  // maps checkpoint ids to the corresponding program counters
  //
  // checkpoint id -> thread -> pc
  //
  std::unordered_map<word_t, std::vector<word_t>> checkpoints;

  // maps program counters to the label referencing it
  //
  // pc -> label
  //
  std::unordered_map<word_t, const std::string *> pc_to_label;

  // maps labels to the corresponding program counter
  //
  // label -> pc
  //
  std::unordered_map<const std::string *, word_t> label_to_pc;

  // jump labels
  //
  std::unordered_set<std::string> labels;

  // next instruction's type
  //
  std::optional<uint8_t> set_type;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  using std::vector<Instruction>::vector; // inherit constructors

  // construct from file
  //
  Program (std::istream & file, const std::string & path);

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // appends instruction to the program
  //
  void push_back (Instruction && op);

  // get pc corresponding to the given label
  //
  word_t get_pc (std::string label) const;

  // get label corresponding to the given pc
  //
  std::string get_label (word_t pc) const;

  // print whole program
  //
  std::string print (bool include_pc = false) const;

  // print instruction at pc
  //
  std::string print (bool include_pc, word_t pc) const;
};

//==============================================================================
// non-member operators
//==============================================================================

// equality
//
bool operator == (const Program &, const Program &);
bool operator != (const Program &, const Program &);

#endif
