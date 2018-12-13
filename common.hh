#ifndef COMMON_HH_
#define COMMON_HH_

#include <limits>

/* machine type ***************************************************************/

typedef unsigned short  word;
typedef short           signed_word;

const   word            word_max  = std::numeric_limits<word>::max();
const   word            word_size = std::numeric_limits<word>::digits;

/* global variables ***********************************************************/

/* verbose output */
extern bool             verbose;

/* end of line character */
const char              eol = '\n';

#endif
