#include "parser.hh"

#include <tuple>
#include <limits>

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

/* Parser<Result>::skipLine (void) ********************************************/
template <typename Result>
void Parser<Result>::skipLine ()
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
      parse(); // TODO: throw something if parse fails
      file.close();
    }
  else
    cout << path << " not found" << endl;
}

/* Parser<Program>::parse (void) **********************************************/
template <>
bool Parser<Program>::parse ()
{
  string token;
  InstructionPtr i;

  /* store machine type's maximum value (used for dummy arguments) */
  word wordMax = numeric_limits<word>::max();

  /* maps label occurrences to the according pc */
  unordered_map<string, word> labelDef;

  /* list of jump instructions at pc referencing a certain label */
  deque<tuple<string, word, string>> labelRef;

  while (file && file >> token)
    {
      /* comment block started? */
      if (token.front() == '#')
        {
          skipLine();
          continue;
        }
      /* found label? */
      else if (token.back() == ':')
        {
          word pc = result->size();
          string label = token.substr(0, token.size() - 1);

          /* store label and the pc it was defined */
          labelDef[label] = pc;
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
              /* try to parse the argument - could be a label */
              word arg;
              if (file >> arg)
                {
                  i = Instruction::Set::create(token, arg);
                  break;
                }
              /* check if command supports labels */
              else
                {
                  /* create dummy Instruction (arg == max(word)) which will be
                     replaced by the actual one when all labels are known */
                  i = Instruction::Set::create(token, wordMax);

                  /* check if the instruction supports labels (is a jmp) */
                  if (dynamic_pointer_cast<Jmp>(i))
                    {
                      /* clear failbit - recover ifstream */
                      file.clear();

                      /* get the label */
                      string label;
                      file >> label;

                      /* get the program counter */
                      word pc = static_cast<word>(result->size());

                      /* add tuple to the list of labelled jumps */
                      labelRef.push_back(make_tuple(token, pc, label));

                      break;
                    }
                  /* error: not a jump instruction */
                  else
                    {
                      cout << "error: " <<
                        token << " does not support labels" << endl;
                      return false;
                    }
                }
            }
        default:
          /* unrecognized token */
          cout << "error: " << token << " unknown token" << endl;
          return false;
        }

      result->add(i);
    }

  /* replace labelled dummy instructions */
  for (auto t : labelRef)
    {
      /* check if label exists */
      // TODO: throws exception on invalid idx
      word arg = labelDef.at(get<2>(t));

      /* create the actual instruction */
      i = Instruction::Set::create(get<0>(t), arg);

      /* replace the dummy */
      (*result)[get<1>(t)] = i;
    }

  return true;
}

/* Parser<Schedule>::parse (void) *********************************************/
template <>
bool Parser<Schedule>::parse ()
{
  string token;

  bool foundSeed = false;

  /* parse header */
  while (file && !foundSeed)
    {
      if (file.peek() == '#')
        {
          skipLine();
          continue;
        }

      file >> token;

      if (token == "seed")
        {
          if (file >> token && token != "=")
            {
              cout << "parser error: = expected" << endl;
              return false;
            }

          file >> result->seed;
          foundSeed = true;
        }
      else
        {
          ThreadID tid = stoul(token, nullptr, 0);

          if (file >> token && token != "=")
            {
              cout << "parser error: = expected" << endl;
              return false;
            }

          file >> token;

          result->add(tid, make_shared<Program>(token));
        }
    }

  /* parse body */
  while (file && file >> token)
    {
      if (token[0] == '#')
        {
          skipLine();
          continue;
        }

      ThreadID tid = stoul(token, nullptr, 0);

      result->add(tid);

      /* ignore rest of the line (in case of verbose output) */
      skipLine();
    }

  return true;
}

/* explicit template instantiations *******************************************/
template class Parser<Program>;
template class Parser<Schedule>;
