// /***********************************************************************/
// /*                                                                     */
// /*                        Applied Type System                          */
// /*                                                                     */
// /*                             Hongwei Xi                              */
// /*                                                                     */
// /***********************************************************************/

// /*
//  * ATS/Anairiats - Unleashing the Power of Types!
//  *
//  * Copyright (C) 2002-2008 Hongwei Xi.
//  *
//  * All rights reserved
//  *
//  * ATS is free software;  you can  redistribute it and/or modify it under
//  * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
//  * Free Software Foundation; either version 3, or (at  your  option)  any
//  * later version.
//  * 
//  * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
//  * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
//  * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
//  * for more details.
//  * 
//  * You  should  have  received  a  copy of the GNU General Public License
//  * along  with  ATS;  see the  file COPYING.  If not, please write to the
//  * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
//  * 02110-1301, USA.
//  *
//  */

// /* ****** ****** */

// June 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

// /* ****** ****** */

// /* [gc.hats]: the header file for GC implementation */
// /* [gc.hats]: it can be used both in ATS and C */

// /* ****** ****** */

// __WORDSIZE = 32 or 64
// #print "__WORDSIZE = "; #print __WORDSIZE; #print "\n"

// /*
// #define __WORDSIZE 32
// */

// /*
#define __WORDSIZE 64
// */

#define NBIT_PER_BYTE 8
#define NBIT_PER_BYTE_LOG 3
#define NBIT_PER_BYTE_MASK (NBIT_PER_BYTE - 1)

// #assert (NBIT_PER_BYTE == 1 << NBIT_PER_BYTE_LOG)
#if (NBIT_PER_BYTE != 1 << NBIT_PER_BYTE_LOG)
#error "#assert (NBIT_PER_BYTE != 1 << NBIT_PER_BYTE_LOG)\n"
#endif

// /* ****** ****** */

#if (__WORDSIZE == 32)
#define NBIT_PER_WORD 32
#define NBIT_PER_WORD_LOG 5

// #assert (NBIT_PER_WORD == 1 << NBIT_PER_WORD_LOG)
#if (NBIT_PER_WORD != 1 << NBIT_PER_WORD_LOG)
#error "#assert (NBIT_PER_WORD == 1 << NBIT_PER_WORD_LOG)\n"
#endif

#define NBYTE_PER_WORD 4
#define NBYTE_PER_WORD_LOG 2

// #assert (NBYTE_PER_WORD == 1 << NBYTE_PER_WORD_LOG)
#if (NBYTE_PER_WORD != 1 << NBYTE_PER_WORD_LOG)
#error "#assert (NBYTE_PER_WORD == 1 << NBYTE_PER_WORD_LOG)\n"
#endif

#endif // end of [__WORDSIZE == 32]

// /* ****** ****** */

#if (__WORDSIZE == 64)
#define NBIT_PER_WORD 64
#define NBIT_PER_WORD_LOG 6

// #assert (NBIT_PER_WORD == 1 << NBIT_PER_WORD_LOG)
#if (NBIT_PER_WORD != 1 << NBIT_PER_WORD_LOG)
#error "#assert (NBIT_PER_WORD == 1 << NBIT_PER_WORD_LOG)\n"
#endif


#define NBYTE_PER_WORD 8
#define NBYTE_PER_WORD_LOG 3

// #assert (NBYTE_PER_WORD == 1 << NBYTE_PER_WORD_LOG)
#if (NBYTE_PER_WORD != 1 << NBYTE_PER_WORD_LOG)
#error "#assert (NBYTE_PER_WORD == 1 << NBYTE_PER_WORD_LOG)\n"
#endif

#endif // end of [__WORDSIZE == 64]

//

#define NBYTE_PER_WORD_MASK (NBYTE_PER_WORD - 1)

// /* ****** ****** */

#define PTR_CHKSEG_SIZE 11
#define PTR_BOTSEG_SIZE 10
#define PTR_BOTCHKSEG_SIZE (PTR_BOTSEG_SIZE + PTR_CHKSEG_SIZE)
#define PTR_TOPSEG_SIZE (NBIT_PER_WORD - PTR_BOTCHKSEG_SIZE - NBYTE_PER_WORD_LOG)
// #print "PTR_TOPSEG_SIZE = "; #print PTR_TOPSEG_SIZE; #print "\n"

#if (__WORDSIZE == 32)
#define TOPSEG_TABLESIZE (1 << PTR_TOPSEG_SIZE)
#endif

#if (__WORDSIZE == 64)
#define TOPSEG_HASHTABLESIZE 4096
#define TOPSEG_HASHTABLESIZE_LOG 12

// #assert (TOPSEG_HASHTABLESIZE == 1 << TOPSEG_HASHTABLESIZE_LOG)
#if (TOPSEG_HASHTABLESIZE != 1 << TOPSEG_HASHTABLESIZE_LOG)
#error "#assert (TOPSEG_HASHTABLESIZE == 1 << TOPSEG_HASHTABLESIZE_LOG)\n"
#endif

#endif // end of [__WORDSIZE == 64]

//

#define CHKSEG_TABLESIZE 2048

// #assert (CHKSEG_TABLESIZE == 1 << PTR_CHKSEG_SIZE)
#if (CHKSEG_TABLESIZE != 1 << PTR_CHKSEG_SIZE)
#error "assert (CHKSEG_TABLESIZE == 1 << PTR_CHKSEG_SIZE)\n"
#endif

//

#define BOTSEG_TABLESIZE 1024

// #assert (BOTSEG_TABLESIZE == 1 << PTR_BOTSEG_SIZE)
#if (BOTSEG_TABLESIZE != 1 << PTR_BOTSEG_SIZE)
#error "assert (BOTSEG_TABLESIZE == 1 << PTR_BOTSEG_SIZE)\n"
#endif

#define BOTSEG_TABLESIZE_MASK (BOTSEG_TABLESIZE - 1)

//

#define CHUNK_WORDSIZE_LOG PTR_CHKSEG_SIZE
#define CHUNK_WORDSIZE (1 << CHUNK_WORDSIZE_LOG)
#define CHUNK_WORDSIZE_MASK (CHUNK_WORDSIZE - 1)
#define CHUNK_BYTESIZE_LOG (CHUNK_WORDSIZE_LOG + NBYTE_PER_WORD_LOG)
#define CHUNK_BYTESIZE (CHUNK_WORDSIZE << NBYTE_PER_WORD_LOG)
#define CHUNK_BYTESIZE_MASK (CHUNK_BYTESIZE - 1)

//

#define MAX_CHUNK_BLOCK_WORDSIZE_LOG CHUNK_WORDSIZE_LOG
#define MAX_CHUNK_BLOCK_WORDSIZE (1 << MAX_CHUNK_BLOCK_WORDSIZE_LOG)
// #assert (MAX_CHUNK_BLOCK_WORDSIZE <= CHUNK_WORDSIZE)

//

// the_freeitmlst_array:
//   [ 2^0 | 2^1 | ... | 2^MAX_CHUNK_BLOCK_WORDSIZE_LOG]
#define FREEITMLST_ARRAYSIZE (MAX_CHUNK_BLOCK_WORDSIZE_LOG + 1)

//

#define MARKSTACK_PAGESIZE 4000
#define MARKSTACK_CUTOFF (CHUNK_WORDSIZE / 4)
#define CHUNK_SWEEP_CUTOFF 0.75 // 75%
// #assert (0.0 <= CHUNK_SWEEP_CUTOFF_PERCENT)
// #assert (CHUNK_SWEEP_CUTOFF_PERCENT <= 1.0)
#define CHUNK_LIMIT_EXTEND_CUTOFF 0.75 // 75%
// #assert (0.0 <= CHUNK_LIMIT_EXTEND_CUTOFF_PERCENT)
// #assert (CHUNK_LIMIT_EXTEND_CUTOFF_PERCENT <= 1.0)

//

#define GLOBALENTRYPAGESIZE 64 // largely chosen arbitrarily

//

#define ATS_GC_RUNTIME_CHECK 0
// #define ATS_GC_RUNTIME_CHECK 1

// /* ****** ****** */

// /* end of [gc.hats] */
