#include "parser.hh"

#include <tuple>
#include <sstream>

#include "program.hh"
#include "schedule.hh"

using namespace std;

/* constructor ****************************************************************/
template <typename Result>
Parser<Result>::Parser(string & p) :
  skip(false),
  path(p),
  file(p),
  result(nullptr)
{}

/* Parser<Result>::skip_line (void) *******************************************/
template <typename Result>
void Parser<Result>::skip_line ()
{
  string line;
  getline(file, line);
}

/* Parser<Result>::parse (void) ***********************************************/
template <typename Result>
void Parser<Result>::parse (Result * r)
{
  result = r;

  if (file.is_open())
    {
      parse();
      file.close();
    }
  else
    throw runtime_error(path + " not found");
}

/* Parser<Program>::parse (void) **********************************************/
template <>
void Parser<Program>::parse ()
{
  string token;
  InstructionPtr i;

  /* maps label occurrences to the according pc */
  unordered_map<string, word> label_def;

  /* list of jump instructions at pc referencing a certain label */
  deque<tuple<string, word, string>> label_ref;

  while (file && file >> token)
    {
      /* comment block started? */
      if (token.front() == '#')
        {
          skip_line();
          continue;
        }
      /* found label? */
      else if (token.back() == ':')
        {
          word pc = result->size();
          string label = token.substr(0, token.size() - 1);

          /* store label and the pc it was defined */
          label_def[label] = pc;
          result->labels[pc] = label;

          /* read labelled command */
          file >> token;
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
            {
              word arg;

              /* try to parse the argument */
              if (file >> arg)
                {
                  i = Instruction::Set::create(token, arg);
                }
              /* label or indirect addressing */
              else
                {
                  /* clear failbit - recover ifstream */
                  file.clear();

                  /* discard leading whitespaces for later use of peek */
                  file >> ws;

                  /* arg is an indirect memory address */
                  if (file.peek() == '[')
                    {
                      /* parse enclosed address */
                      string tmp;
                      file >> tmp;

                      istringstream addr(tmp.substr(1, tmp.size() - 2));

                      /* check if address is a number */
                      if (!(addr >> arg))
                        throw runtime_error(
                          "indirect addressing does not support labels");

                      i = Instruction::Set::create(token, arg);

                      /* check if the instruction supports indirect addresses */
                      if (auto m = dynamic_pointer_cast<MemoryInstruction>(i))
                        m->indirect = true;
                      else
                        throw runtime_error(
                          token +
                          " does not support indirect addressing");
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
                          file >> label;

                          /* get the program counter */
                          word pc = static_cast<word>(result->size());

                          /* add tuple to the list of labelled jumps */
                          label_ref.push_back(make_tuple(token, pc, label));
                        }
                      /* error: not a jump instruction */
                      else
                        throw runtime_error(
                          token +
                          " does not support labels");
                    }
                }
              break;
            }
        default: /* unrecognized token */
          throw runtime_error("'" + token + "'" + " unknown token");
        }

      result->add(i);
    }

  /* replace labelled dummy instructions */
  for (auto t : label_ref)
    {
      /* check if label exists */
      // NOTE: throws exception on invalid idx
      word arg = label_def.at(get<2>(t));

      /* create the actual instruction */
      i = Instruction::Set::create(get<0>(t), arg);

      /* replace the dummy */
      (*result)[get<1>(t)] = i;
    }
}

/* Parser<Schedule>::parse (void) *********************************************/
template <>
void Parser<Schedule>::parse ()
{
  string token;

  bool found_seed = false;

  /* parse header */
  while (file && !found_seed)
    {
      if (file.peek() == '#')
        {
          skip_line();
          continue;
        }

      file >> token;

      /* parse seed */
      if (token == "seed")
        {
          if (file >> token && token != "=")
            throw runtime_error("'=' expected");

          file >> token;

          try
            {
              result->seed = stoul(token, nullptr, 0);
              found_seed = true;
            }
          catch (const exception & e)
            {
              throw runtime_error("illegal seed [" + token + "]");
            }
        }
      /* parse header */
      else
        {
          ThreadID tid;

          try
            {
              tid = stoul(token, nullptr, 0);
            }
          catch (const exception & e)
            {
              throw runtime_error("illegal thread id [" + token + "]");
            }

          if (file >> token && token != "=")
            throw runtime_error("'=' expected");

          file >> token;

          result->add(tid, make_shared<Program>(token));
        }
    }

  /* check header */
  if (result->programs.empty())
    throw runtime_error("missing threads");

  /* parse body */
  while (file && file >> token)
    {
      if (token[0] == '#')
        {
          skip_line();
          continue;
        }

      /* try to parse thread id */
      ThreadID tid;

      try
        {
          tid = stoul(token, nullptr, 0);
        }
      catch (const exception & e)
        {
          throw runtime_error("illegal thread id [" + token + "]");
        }

      if (tid >= result->programs.size() || result->programs[tid] == nullptr)
          throw runtime_error("unknown thread id");

      result->add(tid);

      /* ignore rest of the line (in case of verbose output) */
      skip_line();
    }
}

/* explicit template instantiations *******************************************/
template struct Parser<Program>;
template struct Parser<Schedule>;
