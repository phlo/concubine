/*  ConcuBinE
 *
 *  Copyright (C) 2020 Florian Schrögendorfer.
 *
 *  This file is part of ConcuBinE.
 *  See LICENSE for more information on using this software.
 */

#ifndef PUBLICATE_H_
#define PUBLICATE_H_

#ifdef __TEST__

// disable clang warning about redefining keywords
// #if defined(__APPLE__) && defined (__MACH__)
#ifdef __clang__
#pragma clang diagnostic ignored "-Wkeyword-macro"
#endif

// make all class members public
#define private public
#define protected public

#endif // __TEST__

#endif
