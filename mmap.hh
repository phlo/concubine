#ifndef MMAP_HH_
#define MMAP_HH_

#include <map>

#include "common.hh"

namespace ConcuBinE {

//==============================================================================
// MMap class
//==============================================================================

struct MMap : std::map<word_t, word_t>
{
  //----------------------------------------------------------------------------
  // member types
  //----------------------------------------------------------------------------

  //----------------------------------------------------------------------------
  // members
  //----------------------------------------------------------------------------

  // path to memory map file
  //
  std::string path;

  //----------------------------------------------------------------------------
  // constructors
  //----------------------------------------------------------------------------

  // inherit base constructors
  //
  using std::map<word_t, word_t>::map;

  // construct from file
  //
  MMap (std::istream & file, const std::string & path);

  //----------------------------------------------------------------------------
  // member functions
  //----------------------------------------------------------------------------

  // print memory map
  //
  std::string print () const;
};

//==============================================================================
// non-member operators
//==============================================================================

} // namespace ConcuBinE

#endif