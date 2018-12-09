#ifndef PARSER_HH_
#define PARSER_HH_

#include <string>
#include <fstream>

/*******************************************************************************
 * Parser
 ******************************************************************************/
template <typename Result>
struct Parser
{
  Parser (std::string &);

  bool            skip;
  std::string     path;
  std::ifstream   file;
  Result *        result;

  void            skip_line (void);

  void            parse (void);

  void            parse (Result *);
};

#endif
