#ifndef COMMON_HH_
#define COMMON_HH_

#include <cstdint>
#include <limits>
#include <random>

namespace ConcuBinE {

//==============================================================================
// types
//==============================================================================

// register value
//
using word_t = uint16_t;
using sword_t = int16_t; // signed

//==============================================================================
// constants
//==============================================================================

// register type attributes
//
constexpr word_t word_size = std::numeric_limits<word_t>::digits;
constexpr word_t word_max  = std::numeric_limits<word_t>::max();

constexpr sword_t sword_min  = std::numeric_limits<sword_t>::min();
constexpr sword_t sword_max  = std::numeric_limits<sword_t>::max();

// end of line character
//
constexpr char eol = '\n';

//==============================================================================
// global variables
//==============================================================================

// verbose output
//
extern bool verbose;

// seed used by random number generators
//
extern uint64_t seed;

} // namespace ConcuBinE

#endif
