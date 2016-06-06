#ifndef PARSER_HH_
#define PARSER_HH_

#include <string>
#include <vector>
#include <fstream>
#include <iostream>

using namespace std;

/*******************************************************************************
 * Parser
 ******************************************************************************/
template <typename Result>
class Parser
{
  bool      skip;
  string    path;
  ifstream  file;
  Result *  result;

  void      skipLine (void);

  bool      parse (void);

public:
  Parser (string &);

  void parse (Result *);
};
#endif
