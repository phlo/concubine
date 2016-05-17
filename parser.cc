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
  /* valid token found */
  if (InstructionSet::factory.find(cmd) != InstructionSet::factory.end())
    {
      Instruction * i = InstructionSet::factory[cmd]();

      if (UnaryInstruction * u = dynamic_cast<UnaryInstruction *>(i))
        {
          short arg;
          if (file >> arg)
            {
              u->setArg(arg);
              program->add(shared_ptr<UnaryInstruction>(u));
            }
          else
            return false;
        }
      else
        program->add(shared_ptr<Instruction>(i));

      skip = false;
    }
  /* comment block started */
  else if (skip || cmd[0] == '#')
    {
      skip = true;
    }
  /* unrecognized token */
  else
    {
      cout << "error: " << cmd << " unknown token" << endl;
      return false;
    }

  return true;
}
