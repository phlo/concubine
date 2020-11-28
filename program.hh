/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <istream>
#include <set>
#include <unordered_map>
#include <vector>

#include "common.hh"
#include "instruction.hh"

namespace ConcuBinE {

//==============================================================================
// Program class
//==============================================================================

class Program : public std::vector<Instruction>
{
public: //======================================================================

  //----------------------------------------------------------------------------
  // public member types
  //----------------------------------------------------------------------------

  struct List : public std::vector<Program>
    {
      //------------------------------------------------------------------------
      // public constructors
      //------------------------------------------------------------------------

      // expose constructors from std::vector
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
  // public constructors
  //----------------------------------------------------------------------------

  // expose constructors from std::vector
  //
  using std::vector<Instruction>::vector;

  // parse input stream
  //
  Program (std::istream & stream, const std::string & path);

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // get map of program counters to set of predecessors
  //
  // pc -> set of predecessors
  //
  // * checks for unreachable instructions
  //
  std::unordered_map<word_t, std::set<word_t>> predecessors () const;

  // get program counter corresponding to a given label
  //
  word_t pc (const std::string & label) const;

  // get label corresponding to a given program counter
  //
  std::string label (word_t pc) const;

  // print whole program
  //
  std::string print () const;

  // print instruction at a given program counter
  //
  std::string print (word_t pc) const;

  //----------------------------------------------------------------------------
  // public data members
  //----------------------------------------------------------------------------

  // path to program file
  //
  std::string path;

private: //=====================================================================

  //----------------------------------------------------------------------------
  // private data members
  //----------------------------------------------------------------------------

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
};

} // namespace ConcuBinE

#endif
