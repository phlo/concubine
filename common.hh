#ifndef COMMON_HH_
#define COMMON_HH_

#include <limits>

/* Machine Type ***************************************************************/
typedef unsigned short  word;
typedef short           signed_word;

const   word            word_max  = std::numeric_limits<word>::max();
const   word            word_size = std::numeric_limits<word>::digits;

/* Global Flags ***************************************************************/
extern bool             verbose;

#endif
