#ifndef COMMON_HH_
#define COMMON_HH_

#include <cstdint>
#include <limits>

/* machine type ***************************************************************/

typedef uint16_t  word;
typedef int16_t   signed_word;

const   word      word_max  = std::numeric_limits<word>::max();
const   word      word_size = std::numeric_limits<word>::digits;

/* global variables ***********************************************************/

/* verbose output */
extern bool       verbose;

/* end of line character */
const char        eol = '\n';

#endif
