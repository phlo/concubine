#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <istream>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common.hh"

namespace ConcuBinE {

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

  // program list --------------------------------------------------------------
  //
  struct List : public std::vector<Program>
    {
      using ptr = std::shared_ptr<List>;

      //------------------------------------------------------------------------
      // constructors
      //------------------------------------------------------------------------

      // inherit constructors from std::vector
      //
      using std::vector<Program>::vector;

      // alias for checking if parameter pack is of class T
      //
      template <typename T, typename ... Ts>
      using all_base_of = std::conjunction<std::is_base_of<T, Ts>...>;

      // alias for restricting variadic overloads to parameters of class T
      //
      template <typename T, typename ... Ts>
      using enable_if_all_base_of =
        typename std::enable_if<all_base_of<T, Ts...>::value>::type;

      // variadic copy constructor for arguments of type Program
      //
      template <class ... Ts, typename = enable_if_all_base_of<Program, Ts...>>
      List (const Ts & ... program) : std::vector<Program>()
        {
          reserve(sizeof...(Ts));
          (push_back(program), ...);
        }

      // variadic move constructor for arguments of type Program
      //
      template <class ... Ts, typename = enable_if_all_base_of<Program, Ts...>>
      List (Ts && ... program) : std::vector<Program>()
        {
          reserve(sizeof...(Ts));
          (push_back(std::move(program)), ...);
        }
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
  std::unordered_map<word_t, std::string> pc_to_label;

  // maps labels to the corresponding program counter
  //
  // label -> pc
  //
  std::unordered_map<std::string, word_t> label_to_pc;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  // inherit base constructors
  //
  using std::vector<Instruction>::vector;

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
// TODO: really needed - rely on base class?
//
bool operator == (const Program &, const Program &);
bool operator != (const Program &, const Program &);

} // namespace ConcuBinE

#endif
