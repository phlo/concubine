#include "program.hh"

#include <sstream>

#include "parser.hh"

using namespace std;

/* default constructor ********************************************************/
Program::Program() {}

/* construct from file ********************************************************/
Program::Program(istream & file, string & name) : path(name)
{
  string token;

  InstructionPtr cmd;

  unsigned long line_num = 1;

  /* list of jump instructions at pc referencing a certain label */
  deque<tuple<string, word, const string *>> labelled_jumps;

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

      /* parse instruction */
      switch (Instruction::Set::contains(symbol))
        {
        case Instruction::Type::NULLARY:
            {
              cmd = Instruction::Set::create(symbol);
              break;
            }
        case Instruction::Type::UNARY:
        case Instruction::Type::MEMORY:
            {
              word arg;

              /* try to parse the argument */
              if (line >> arg)
                {
                  cmd = Instruction::Set::create(symbol, arg);
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

                      istringstream addr(token.substr(1, token.size() - 2));

                      /* check if address is a number */
                      if (!(addr >> arg))
                        parser_error(
                          path,
                          line_num,
                          "indirect addressing does not support labels");

                      cmd = Instruction::Set::create(symbol, arg);

                      /* check if the instruction supports indirect addresses */
                      if (auto m = dynamic_pointer_cast<MemoryInstruction>(cmd))
                        m->indirect = true;
                      else
                        parser_error(
                          path,
                          line_num,
                          symbol + " does not support indirect addressing");
                    }
                  /* arg is a label */
                  else
                    {
                      /* create dummy Instruction which will be replaced by the
                         actual one when all labels are known */
                      cmd = Instruction::Set::create(symbol, word_max);

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
                        parser_error(
                          path,
                          line_num,
                          symbol + " does not support labels");
                    }
                }
              break;
            }
        default: /* unrecognized token */
          parser_error(
            path,
            line_num,
            "'" + symbol + "'" + " unknown instruction");
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

/* Program::push_back (InstructionPtr) ****************************************/
void Program::push_back (InstructionPtr i)
{
  deque<InstructionPtr>::push_back(i);

  /* collect sync barrier ids */
  if (SyncPtr s = dynamic_pointer_cast<Sync>(i))
    sync_ids.insert(s->arg);
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
  InstructionPtr cmd = at(pc);
  ss << cmd->get_symbol() << "\t";

  /* print unary instruction's argument */
  if (UnaryInstructionPtr u = dynamic_pointer_cast<UnaryInstruction>(cmd))
    {
      label_it = pc_to_label.find(u->arg);
      if (dynamic_pointer_cast<Jmp>(cmd) && label_it != pc_to_label.end())
        ss << *label_it->second;
      else if (auto m = dynamic_pointer_cast<MemoryInstruction>(u))
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
