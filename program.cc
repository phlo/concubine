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

  InstructionPtr i;

  unsigned long line_num = 1;

  /* maps label occurrences to the according pc */
  unordered_map<string, word> label_def;

  /* list of jump instructions at pc referencing a certain label */
  deque<tuple<string, word, string>> label_ref;

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
          string label = token.substr(0, token.size() - 1);

          /* store label and the pc it was defined */
          label_def[label] = pc;
          labels[pc] = label;

          /* read labelled command */
          line >> token;
        }

      /* parse instruction */
      switch (Instruction::Set::contains(token))
        {
        case Instruction::Type::NULLARY:
            {
              i = Instruction::Set::create(token);
              break;
            }
        case Instruction::Type::UNARY:
        case Instruction::Type::MEMORY:
            {
              word arg;

              /* try to parse the argument */
              if (line >> arg)
                {
                  i = Instruction::Set::create(token, arg);
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
                      string tmp;
                      line >> tmp;

                      istringstream addr(tmp.substr(1, tmp.size() - 2));

                      /* check if address is a number */
                      if (!(addr >> arg))
                        parser_error(
                          path,
                          line_num,
                          "indirect addressing does not support labels");

                      i = Instruction::Set::create(token, arg);

                      /* check if the instruction supports indirect addresses */
                      if (auto m = dynamic_pointer_cast<MemoryInstruction>(i))
                        m->indirect = true;
                      else
                        parser_error(
                          path,
                          line_num,
                          token + " does not support indirect addressing");
                    }
                  /* arg is a label */
                  else
                    {
                      /* create dummy Instruction which will be replaced by the
                         actual one when all labels are known */
                      i = Instruction::Set::create(token, word_max);

                      /* check if the instruction supports labels (is a jmp) */
                      if (dynamic_pointer_cast<Jmp>(i))
                        {
                          /* get the label */
                          string label;
                          line >> label;

                          /* get the program counter */
                          word pc = size();

                          /* add tuple to the list of labelled jumps */
                          label_ref.push_back(make_tuple(token, pc, label));
                        }
                      /* error: not a jump instruction */
                      else
                        parser_error(
                          path,
                          line_num,
                          token + " does not support labels");
                    }
                }
              break;
            }
        default: /* unrecognized token */
          parser_error(path, line_num, "'" + token + "'" + " unknown token");
        }

      add(i);
    }

  /* replace labelled dummy instructions */
  for (const auto & [cmd, pc, label] : label_ref)
    {
      /* check if label exists */
      // NOTE: throws exception on invalid idx
      word arg = label_def.at(label);

      /* create the actual instruction */
      i = Instruction::Set::create(cmd, arg);

      /* replace the dummy */
      at(pc) = i;
    }
}

/* Program::add (InstructionPtr) **********************************************/
void Program::add (InstructionPtr i)
{
  push_back(i);

  /* collect sync barrier ids */
  if (SyncPtr s = dynamic_pointer_cast<Sync>(i))
    sync_ids.insert(s->arg);
}

/* Program::print (bool) ******************************************************/
string Program::print (bool include_pc)
{
  ostringstream ss;

  for (word i = 0; i < size(); i++)
    ss <<  print(include_pc, i) << eol;

  return ss.str();
}

/* Program::print (bool, word) ************************************************/
string Program::print (bool include_pc, word pc)
{
  ostringstream ss;

  /* check if instruction can be referenced by a label */
  if (labels.find(pc) != labels.end())
    {
      ss << labels[pc];

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
      if (dynamic_pointer_cast<Jmp>(cmd) && labels.find(u->arg) != labels.end())
        ss << labels[u->arg];
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
