#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <deque>
#include <unordered_set>

#include "instructionset.hh"

/*******************************************************************************
 * Program
 ******************************************************************************/
struct Program : public std::deque<InstructionPtr>
{
  /* default constructor (for testing) */
  Program (void);

  /* construct from file */
  Program (std::string);

  /* path to program file */
  std::string                             path;

  /* sync barriers */
  std::unordered_set<word>                syncIDs;

  /* maps program counters to the label referencing it */
  std::unordered_map<word, std::string>   labels;

  /* appends instruction to the program */
  void                                    add (InstructionPtr);

  /* print whole program */
  std::string                             print (bool);

  /* print instruction at pc */
  std::string                             print (bool, word);
};

/*******************************************************************************
 * ProgramPtr
 ******************************************************************************/
typedef std::shared_ptr<Program>          ProgramPtr;

/*******************************************************************************
 * ProgramList
 ******************************************************************************/
typedef std::deque<ProgramPtr>            ProgramList;

/*******************************************************************************
 * ProgramListPtr
 ******************************************************************************/
typedef std::shared_ptr<ProgramList>      ProgramListPtr;

#endif
