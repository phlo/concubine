#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <deque>
#include <unordered_set>
#include <unordered_map>

#include "parser.hh"
#include "instructionset.hh"

/*******************************************************************************
 * Program
 ******************************************************************************/
class Program : public deque<InstructionPtr>
{
  /* be friends with the Parser - for a minimal public interface */
  friend class Parser<Program>;

  string                        path;

  unordered_set<word>           syncIDs;

  unordered_map<word, string>   labels;

public:
  Program (string &);

  void                          add (InstructionPtr);

  string &                      getPath (void);

  unordered_set<word> &         getSyncIDs (void);

  unordered_map<word, string> & getLabels(void);
};

/*******************************************************************************
 * ProgramPtr
 ******************************************************************************/
typedef shared_ptr<Program> ProgramPtr;

#endif
