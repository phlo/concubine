/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#include "program.hh"

#include <sstream>

#include "instruction.hh"
#include "parser.hh"

namespace ConcuBinE {

//==============================================================================
// macros
//==============================================================================

#define PARSER_ERROR(msg) do { parser_error(path, line_num, msg); } while (0)
#define INSTRUCTION_ERROR(msg) PARSER_ERROR("'" + symbol + "' " + msg)
#define UNKNOWN_INSTRUCTION_ERROR() INSTRUCTION_ERROR("unknown instruction")

//==============================================================================
// Program
//==============================================================================

//------------------------------------------------------------------------------
// public constructors
//------------------------------------------------------------------------------

Program::Program (std::istream & is, const std::string & p) : path(p)
{
  // list of jump instructions at pc referencing a certain label
  std::vector<std::pair<word_t, std::string>> labelled_jumps;

  size_t line_num = 1;
  for (std::string line_buf, token; std::getline(is, line_buf); line_num++)
    {
      // skip empty lines
      if (line_buf.empty())
        continue;

      std::istringstream line(line_buf);

      // skip comments
      if (line >> token && token.front() == '#')
        continue;

      // found label?
      else if (token.back() == ':')
        {
          const word_t pc = size();
          const std::string label = token.substr(0, token.size() - 1);

          // store label and the pc it was defined
          label_to_pc[label] = pc;
          pc_to_label[pc] = label;

          // read labelled command
          if (!(line >> token))
            PARSER_ERROR("missing instruction");
        }

      Instruction op;
      std::string symbol(std::move(token));

      if (line.eof())
        {
          try { op = Instruction::create(symbol); }
          catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }
        }
      else
        {
          word_t arg;

          // try to parse the argument
          if (line >> arg)
            {
              try { op = Instruction::create(symbol, arg); }
              catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }
            }
          // label or indirect addressing
          else
            {
              // clear failbit - recover ifstream
              line.clear();

              // discard leading whitespaces for later use of peek
              line >> std::ws;

              // arg is an indirect memory address
              if (line.peek() == '[')
                {
                  // parse enclosed address
                  line >> token;

                  try { arg = stoul(token.substr(1, token.size() - 2)); }
                  catch (std::invalid_argument & e)
                    {
                      PARSER_ERROR(
                        "indirect addressing does not support labels");
                    }

                  try { op = Instruction::create(symbol, arg); }
                  catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }

                  // check if the instruction supports indirect addresses
                  if (!op.is_memory())
                    INSTRUCTION_ERROR("does not support indirect addressing");

                  op.indirect(true);
                }
              // arg is a label
              else
                {
                  // create dummy Instruction
                  try { op = Instruction::create(symbol, word_max); }
                  catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }

                  // check if the instruction supports labels (is a jmp)
                  if (!op.is_jump())
                    INSTRUCTION_ERROR("does not support labels");

                  if (!(line >> token))
                    PARSER_ERROR("missing label");

                  // add to the list of labelled jumps
                  labelled_jumps.push_back(make_pair(size(), token));
                }
            }
        }

      push_back(std::move(op));
    }

  // update labelled instruction's argument
  for (const auto & [pc, label] : labelled_jumps)
    try
      {
        (*this)[pc].arg(label_to_pc.at(label));
      }
    catch (...)
      {
        throw std::runtime_error(path + ": unknown label [" + label + "]");
      }

  // find illegal jumps
  for (word_t pc = 0; pc < size(); pc++)
    {
      const auto & op = (*this)[pc];

      if (op.is_jump() && op.arg() >= size())
        throw
          std::runtime_error(
            path + ": illegal jump [" + std::to_string(pc) + "]");
    }

  // insert final HALT (if missing)
  if (!(back().type() & Instruction::Type::control))
    push_back(Instruction::create("HALT"));
}

//------------------------------------------------------------------------------
// public member functions
//------------------------------------------------------------------------------

// Program::predecessors -------------------------------------------------------

std::unordered_map<word_t, std::set<word_t>> Program::predecessors () const
{
  std::unordered_map<word_t, std::set<word_t>> predecessors;

  // collect predecessors
  for (word_t pc = 0, final = size() - 1; pc <= final; pc++)
    {
      const Instruction & op = (*this)[pc];

      if (op.is_jump())
        {
          if (&op.symbol() != &Instruction::Jmp::symbol)
            predecessors[pc + 1].insert(pc);

          predecessors[op.arg()].insert(pc);
        }
      else if (pc < final)
        {
          using Halt = Instruction::Halt;
          using Exit = Instruction::Exit;

          if (&op.symbol() != &Exit::symbol && &op.symbol() != &Halt::symbol)
            predecessors[pc + 1].insert(pc);
        }
    }

  // check for unreachable instructions
  for (word_t pc = 1; pc < size(); pc++)
    if (predecessors.find(pc) == predecessors.end())
      throw
        std::runtime_error(
          path + ": unreachable instruction [" + std::to_string(pc) + "]");

  return predecessors;
}

// Program::pc -----------------------------------------------------------------

word_t Program::pc (const std::string & label) const
{
  const auto it = label_to_pc.find(label);

  if (it == label_to_pc.end())
    throw std::runtime_error(path + ": unknown label [" + label + "]");

  return it->second;
}

// Program::label --------------------------------------------------------------

std::string Program::label (const word_t pc) const
{
  const auto it = pc_to_label.find(pc);

  if (it == pc_to_label.end())
    throw
      std::runtime_error(path + ": no label for [" + std::to_string(pc) + "]");

  return it->second;
}

// Program::print --------------------------------------------------------------

std::string Program::print () const
{
  std::ostringstream ss;

  for (word_t i = 0; i < size(); i++)
    ss <<  print(i) << eol;

  return ss.str();
}

std::string Program::print (const word_t pc) const
{
  std::ostringstream ss;

  // check if instruction is referenced by a label
  auto label_it = pc_to_label.find(pc);
  if (label_it != pc_to_label.end())
    ss << label_it->second << ": ";

  // instruction symbol
  const Instruction & op = (*this)[pc];

  ss << op.symbol();

  // print unary instruction's argument
  if (op.is_unary())
    {
      ss << ' ';

      label_it = pc_to_label.find(op.arg());
      if (op.is_jump() && label_it != pc_to_label.end())
        {
          ss << label_it->second;
        }
      else if (op.is_memory())
        {
          if (op.indirect())
            ss << "[" << op.arg() << "]";
          else
            ss << op.arg();
        }
      else
        {
          ss << op.arg();
        }
    }

  return ss.str();
}

} // namespace ConcuBinE
