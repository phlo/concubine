#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <deque>
#include <unordered_set>
#include <unordered_map>

#include "parser.hh"
#include "instructionset.hh"

class Program;

/*******************************************************************************
 * ProgramPtr
 ******************************************************************************/
typedef shared_ptr<Program>     ProgramPtr;

/*******************************************************************************
 * ProgramList
 ******************************************************************************/
typedef deque<ProgramPtr>       ProgramList;

/*******************************************************************************
 * ProgramListPtr
 ******************************************************************************/
typedef shared_ptr<ProgramList> ProgramListPtr;

/*******************************************************************************
 * Program
 ******************************************************************************/
class Program : public deque<InstructionPtr>
{
  /* be friends with the Parser - for a minimal public interface */
  friend class Parser<Program>;

  /* path to program file */
  string                        path;

  /* sync barriers */
  unordered_set<word>           syncIDs;

  /* maps program counters to the label referencing it */
  unordered_map<word, string>   labels;

public:
  /* default constructor */
  Program (void);

  /* construct from file (by name) */
  Program (string &);

  /* appends instruction to the program */
  void                          add (InstructionPtr);

  /* returns path to program file */
  string &                      getPath (void);

  /* returns set of contained sync barrier ids */
  unordered_set<word> &         getSyncIDs (void);

  /* returns label map */
  unordered_map<word, string> & getLabels (void);

  /* print whole program */
  void                          print (bool);

  /* print instruction at pc */
  void                          print (bool, word);

  /* unrolls all loops to a given number of iterations */
  ProgramPtr                    unroll (word);
};
#endif
