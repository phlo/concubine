#ifndef PARSER_HH_
#define PARSER_HH_

#include <string>
#include <vector>
#include <fstream>
#include <iostream>

#include "program.hh"

using namespace std;

/*******************************************************************************
 * Parser
 ******************************************************************************/
class Parser
{
  bool      skip;
  string    path;
  ifstream  file;
  Program * program;

  bool      parse (string &);

public:
  Parser (string);

  Program * parse (void);
};
#endif
