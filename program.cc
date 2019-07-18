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
// constructors
//------------------------------------------------------------------------------

Program::Program(std::istream & f, const std::string & p) : path(p)
{
  std::string token;

  Instruction cmd;

  size_t line_num = 1;

  // list of jump instructions at pc referencing a certain label
  std::vector<
    std::tuple<std::string, word_t, const std::string *>> labelled_jumps;

  for (std::string line_buf; std::getline(f, line_buf); line_num++)
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
          word_t pc = size();

          const std::string * label =
            &*labels.insert(token.substr(0, token.size() - 1)).first;

          // store label and the pc it was defined
          label_to_pc[label] = pc;
          pc_to_label[pc] = label;

          // read labelled command
          line >> token;
        }

      std::string symbol = token;

      line >> std::ws;

      // parse instruction
      if (line.eof())
        {
          try { cmd = Instruction::create(symbol); }
          catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }
        }
      else
        {
          word_t arg;

          // try to parse the argument
          if (line >> arg)
            {
              try { cmd = Instruction::create(symbol, arg); }
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

                  try
                    {
                      arg = stoul(token.substr(1, token.size() - 2));
                    }
                  catch (std::invalid_argument & e)
                    {
                      PARSER_ERROR(
                        "indirect addressing does not support labels");
                    }

                  try { cmd = Instruction::create(symbol, arg); }
                  catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }

                  // check if the instruction supports indirect addresses
                  if (cmd.is_memory())
                    cmd = Instruction::create(symbol, arg, true);
                  else
                    INSTRUCTION_ERROR("does not support indirect addressing");
                }
              // arg is a label
              else
                {
                  // create dummy Instruction which will be replaced by the
                  // actual one when all labels are known
                  try { cmd = Instruction::create(symbol, word_max); }
                  catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }

                  // check if the instruction supports labels (is a jmp)
                  if (cmd.is_jump())
                    {
                      // get the label
                      line >> token;

                      // get the program counter
                      word_t pc = size();

                      // add std::tuple to the list of labelled jumps
                      labelled_jumps.push_back(
                        make_tuple(
                          symbol,
                          pc,
                          &*labels.insert(token).first));
                    }
                  // error: not a jump instruction
                  else
                    INSTRUCTION_ERROR("does not support labels");
                }
            }
        }

      push_back(std::move(cmd));
    }

  // replace labelled dummy instructions
  for (const auto & [sym, pc, label] : labelled_jumps)
    try
      {
        // check if label exists and replace dummy
        (*this)[pc] =
          Instruction::create(sym, label_to_pc.at(label));
      }
    catch (...)
      {
        parser_error(path, pc, "unknown label [" + *label + "]");
      }

  // collect predecessors
  predecessors[0]; // explicitly add initial instruction
  for (word_t pc = 0, last = size() - 1; pc <= last; pc++)
    {
      const Instruction & op = (*this)[pc];

      if (op.is_jump())
        {
          const word_t target = op.arg();

          if (target >= size())
            throw std::runtime_error(
              path + ": illegal jump [" + std::to_string(pc) + "]");

          if (op.symbol() != Instruction::Jmp::symbol || target == pc + 1)
            predecessors[pc + 1].insert(pc);

          predecessors[target].insert(pc);
        }
      else if (pc < last)
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
      throw std::runtime_error(
        path + ": unreachable instruction [" + std::to_string(pc) + "]");
}

//------------------------------------------------------------------------------
// member functions
//------------------------------------------------------------------------------

// Program::push_back ----------------------------------------------------------

void Program::push_back (Instruction && op)
{
  // collect checkpoint id
  if (&op.symbol() == &Instruction::Check::symbol)
    checkpoints[op.arg()].push_back(size());

  // append instruction
  std::vector<Instruction>::push_back(op);
}

// Program::get_pc -------------------------------------------------------------

word_t Program::get_pc (const std::string label) const
{
  const auto it = labels.find(label);

  if (it == labels.end())
    throw std::runtime_error("unknown label [" + label + "]");

  return label_to_pc.at(&*it);
}

// Program::get_label ----------------------------------------------------------

std::string Program::get_label (const word_t pc) const
{
  const auto it = pc_to_label.find(pc);

  if (it == pc_to_label.end())
    throw
      std::runtime_error(
        "no label for program counter [" + std::to_string(pc) + "]");

  return *it->second;
}

// Program::print --------------------------------------------------------------

std::string Program::print (const bool include_pc) const
{
  std::ostringstream ss;

  for (word_t i = 0; i < size(); i++)
    ss <<  print(include_pc, i) << eol;

  return ss.str();
}

std::string Program::print (const bool include_pc, const word_t pc) const
{
  std::ostringstream ss;
  const char delimiter = ' ';

  if (include_pc)
    ss << pc << delimiter;

  // check if instruction is referenced by a label
  auto label_it = pc_to_label.find(pc);
  if (label_it != pc_to_label.end())
    ss << *label_it->second << ": ";

  // instruction symbol
  const Instruction & op = (*this)[pc];

  ss << op.symbol();

  // print unary instruction's argument
  if (op.is_unary())
    {
      ss << delimiter;

      label_it = pc_to_label.find(op.arg());
      if (op.is_jump() && label_it != pc_to_label.end())
        {
          ss << *label_it->second;
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

//==============================================================================
// non-member operators
//==============================================================================

// equality --------------------------------------------------------------------
//
bool operator == (const Program & a, const Program & b)
{
  if (a.size() != b.size())
    return false;

  for (size_t i = 0; i < a.size(); i++)
    if (a[i] != b[i])
      return false;

  return true;
}

bool operator != (const Program & a, const Program & b)
{
  return !(a == b);
}

} // namespace ConcuBinE
