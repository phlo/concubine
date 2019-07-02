#ifndef COMMON_HH_
#define COMMON_HH_

#include <cstdint>
#include <limits>

//==============================================================================
// types
//==============================================================================

// register value
//
using word_t = uint16_t;
using sword_t = int16_t; // signed

// model checking step
//
using bound_t = uint64_t;

//==============================================================================
// global variables
//==============================================================================

// word attributes
//
const word_t word_size = std::numeric_limits<word_t>::digits;
const word_t word_max  = std::numeric_limits<word_t>::max();

const sword_t sword_min  = std::numeric_limits<sword_t>::min();
const sword_t sword_max  = std::numeric_limits<sword_t>::max();

// verbose output
//
extern bool verbose;

// end of line character
//
const char eol = '\n';

#endif
