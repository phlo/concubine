#include "parser.hh"

using namespace std;

/* constructor ****************************************************************/
Parser::Parser(string p) : skip(false), path(p), file(p), program(NULL) {}

/* Parser::parse (void) *******************************************************/
Program * Parser::parse ()
{
  if (file.is_open())
    {
      program = new Program(path);
      while (file)
        {
          string token;
          if (file >> token)
            parse(token);
          // TODO: throw something if parse fails
        }
      file.close();
    }
  else
    {
      cout << path << " not found" << endl;
    }

  return program;
}

/* Parser::parse (string) *****************************************************/
bool Parser::parse (string & cmd)
{
  InstructionPtr i;

  switch (Instruction::Set::contains(cmd))
    {
    case Instruction::Type::NULLARY:
        {
          i = Instruction::Set::create(cmd);
          break;
        }
    case Instruction::Type::UNARY:
        {
          word arg;
          if (file >> arg)
            {
              i = Instruction::Set::create(cmd, arg);
              break;
            }
          else
            goto UNKNOWN;
        }
    default:
      /* comment block started? */
      if (skip || cmd[0] == '#')
        {
          return skip = true;
        }
      /* unrecognized token */
      else
        {
UNKNOWN:
          cout << "error: " << cmd << " unknown token" << endl;
          return false;
        }
    }

  program->add(i);

  return true;
}
