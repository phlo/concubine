#include "program.hh"

#include <sstream>
#include <vector>

#include "instructionset.hh"
#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Program::Program() {}

/* construct from file ********************************************************/
#define PARSER_ERROR(msg) do { parser_error(path, line_num, msg); } while (0)
#define INSTRUCTION_ERROR(msg) PARSER_ERROR("'" + symbol + "' " + msg)
#define UNKNOWN_INSTRUCTION_ERROR() INSTRUCTION_ERROR("unknown instruction")

Program::Program(istream & file, string & name) : path(name)
{
  string token;

  Instruction_ptr cmd;

  unsigned long line_num = 1;

  /* list of jump instructions at pc referencing a certain label */
  vector<tuple<string, word, const string *>> labelled_jumps;

  for (string line_buf; getline(file, line_buf); line_num++)
    {
      /* skip empty lines */
      if (line_buf.empty())
        continue;

      istringstream line(line_buf);

      /* skip comments */
      if (line >> token && token.front() == '#')
        continue;

      /* found label? */
      else if (token.back() == ':')
        {
          word pc = size();

          const string * label =
            &*labels.insert(token.substr(0, token.size() - 1)).first;

          /* store label and the pc it was defined */
          label_to_pc[label] = pc;
          pc_to_label[pc] = label;

          /* read labelled command */
          line >> token;
        }

      string symbol = token;

      line >> ws;

      /* parse instruction */
      if (line.eof())
        {
          try { cmd = Instruction::Set::create(symbol); }
          catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }
        }
      else
        {
          word arg;

          /* try to parse the argument */
          if (line >> arg)
            {
              try { cmd = Instruction::Set::create(symbol, arg); }
              catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }
            }
          /* label or indirect addressing */
          else
            {
              /* clear failbit - recover ifstream */
              line.clear();

              /* discard leading whitespaces for later use of peek */
              line >> ws;

              /* arg is an indirect memory address */
              if (line.peek() == '[')
                {
                  /* parse enclosed address */
                  line >> token;

                  try
                    {
                      arg = stoul(token.substr(1, token.size() - 2));
                    }
                  catch (invalid_argument & e)
                    {
                      PARSER_ERROR(
                        "indirect addressing does not support labels");
                    }

                  try { cmd = Instruction::Set::create(symbol, arg); }
                  catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }

                  /* check if the instruction supports indirect addresses */
                  if (auto m = dynamic_pointer_cast<Memory>(cmd))
                    m->indirect = true;
                  else
                    INSTRUCTION_ERROR("does not support indirect addressing");
                }
              /* arg is a label */
              else
                {
                  /* create dummy Instruction which will be replaced by the
                     actual one when all labels are known */
                  try { cmd = Instruction::Set::create(symbol, word_max); }
                  catch (...) { UNKNOWN_INSTRUCTION_ERROR(); }

                  /* check if the instruction supports labels (is a jmp) */
                  if (dynamic_pointer_cast<Jmp>(cmd))
                    {
                      /* get the label */
                      line >> token;

                      /* get the program counter */
                      word pc = size();

                      /* add tuple to the list of labelled jumps */
                      labelled_jumps.push_back(
                        make_tuple(
                          symbol,
                          pc,
                          &*labels.insert(token).first));
                    }
                  /* error: not a jump instruction */
                  else
                    INSTRUCTION_ERROR("does not support labels");
                }
            }
        }

      push_back(cmd);
    }

  /* replace labelled dummy instructions */
  for (const auto & [sym, pc, label] : labelled_jumps)
    {
      /* check if label exists */
      try
        {
          /* create actual instruction and replace dummy */
          at(pc) = Instruction::Set::create(sym, label_to_pc.at(label));
        }
      catch (...)
        {
          parser_error(path, pc, "unknown label [" + *label + "]");
        }
    }
}

/* Program::push_back (Instruction_ptr) ***************************************/
void Program::push_back (Instruction_ptr i)
{
  deque<Instruction_ptr>::push_back(i);

  /* collect checkpoint ids */
  if (Check_ptr c = dynamic_pointer_cast<Check>(i))
    check_ids.insert(c->arg);
}

/* Program::get_pc (const string label) const *********************************/
word Program::get_pc (const string label) const
{
  const auto it = labels.find(label);

  if (it == labels.end())
    throw runtime_error("unknown label [" + label + "]");

  return label_to_pc.at(&*it);
}

/* Program::get_label (const word) const **************************************/
string Program::get_label (const word pc) const
{
  const auto it = pc_to_label.find(pc);

  if (it == pc_to_label.end())
    throw runtime_error("no label for program counter [" + to_string(pc) + "]");

  return *it->second;
}

/* Program::print (bool) const ************************************************/
string Program::print (bool include_pc) const
{
  ostringstream ss;

  for (word i = 0; i < size(); i++)
    ss <<  print(include_pc, i) << eol;

  return ss.str();
}

/* Program::print (bool, word) const ******************************************/
string Program::print (bool include_pc, word pc) const
{
  ostringstream ss;

  /* check if instruction is referenced by a label */
  auto label_it = pc_to_label.find(pc);
  if (label_it != pc_to_label.end())
    {
      ss << *label_it->second;

      if (include_pc)
        ss << "\t";
      else
        ss << ": ";
    }
  else if (include_pc)
    ss << pc << "\t";

  /* instruction symbol */
  Instruction_ptr cmd = at(pc);
  ss << cmd->symbol() << "\t";

  /* print unary instruction's argument */
  if (Unary_ptr u = dynamic_pointer_cast<Unary>(cmd))
    {
      label_it = pc_to_label.find(u->arg);
      if (dynamic_pointer_cast<Jmp>(cmd) && label_it != pc_to_label.end())
        ss << *label_it->second;
      else if (auto m = dynamic_pointer_cast<Memory>(u))
        ss << (m->indirect ? "[" : "") << m->arg << (m->indirect ? "]" : "");
      else
        ss << u->arg;
    }

  return ss.str();
}

/* operator == (const Program &, const Program &) *****************************/
bool operator == (const Program & a, const Program & b)
{
  if (a.size() != b.size())
    return false;

  for (size_t i = 0; i < a.size(); i++)
    if (*a[i] != *b[i])
      return false;

  return true;
}

/* operator != (const Program &, const Program &) *****************************/
bool operator != (const Program & a, const Program & b)
{
  return !(a == b);
}
