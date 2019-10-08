#ifndef MMAP_HH_
#define MMAP_HH_

#include <map>

#include "common.hh"

namespace ConcuBinE {

//==============================================================================
// MMap class
//==============================================================================

struct MMap : public std::map<word_t, word_t>
{
  //----------------------------------------------------------------------------
  // public constructors
  //----------------------------------------------------------------------------

  // expose constructors from std::map
  //
  using std::map<word_t, word_t>::map;

  // parse input stream
  //
  MMap (std::istream & file, const std::string & path);

  //----------------------------------------------------------------------------
  // public member functions
  //----------------------------------------------------------------------------

  // print memory map
  //
  std::string print () const;

  //----------------------------------------------------------------------------
  // public data members
  //----------------------------------------------------------------------------

  // path to memory map file
  //
  std::string path;
};

} // namespace ConcuBinE

#endif
