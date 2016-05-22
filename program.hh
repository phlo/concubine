#ifndef PROGRAM_HH_
#define PROGRAM_HH_

#include <deque>
#include <unordered_set>

#include "instructionset.hh"

/*******************************************************************************
 * Program
 ******************************************************************************/
class Program : public deque<shared_ptr<Instruction>>
{
  string                path;

  unordered_set<word>   syncIDs;

public:
  Program (string &);

  void                  add (InstructionPtr);

  string &              getPath (void);

  unordered_set<word> & getSyncIDs (void);
};

/*******************************************************************************
 * ProgramPtr
 ******************************************************************************/
typedef shared_ptr<Program> ProgramPtr;

#endif
