/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
** ATS/Anairiats - Unleashing the Power of Types!
**
** Copyright (C) 2002-2009 Hongwei Xi.
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

/* ****** ****** */

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// October 2009

/* ****** ****** */

#include "ats_types.h"
#include "ats_basics.h"

/* ****** ****** */

#ifndef ATS_RUNTIME_GCATS2_CATS
#define ATS_RUNTIME_GCATS2_CATS

/* ****** ****** */

#include <stdio.h>
#include <string.h>

#include <sys/mman.h> // for mmap

/* ****** ****** */

#include "gcats2_c.h"

/* ****** ****** */

typedef unsigned char byte ;
typedef ats_ptr_type topseg_t ;

typedef ats_ptr_type freeitmptr_vt ;
typedef ats_ptr_type freeitmlst_vt ;

typedef ats_ptr_type freepageptr_vt ;
typedef ats_ptr_type freepagelst_vt ;

/* ****** ****** */

//
// external malloc/free functions for GCATS2
//

static inline
ats_ptr_type
gcats2_malloc_ext (ats_int_type bsz) {
  void *p ;
/*
  fprintf(stderr, "gcats2_malloc_ext: bsz = %i\n", bsz) ;
*/
  p = malloc(bsz) ;
  if (p == (void*)0) {
    fprintf(stderr, "exit(ATS/GC): external memory is unavailable.\n"); exit(1);
  } /* end of [if] */
  return p ;
} /* end of [gcats2_malloc_ext] */

static inline
ats_ptr_type
gcats2_free_ext (ats_ptr_type ptr) { free(ptr); return ; }

/* ****** ****** */

static inline
ats_bool_type
gcats2_freeitmlst_isnil (ats_ptr_type xs) {
  return (xs == (freeitmlst_vt*)0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
gcats2_freeitmlst_iscons (ats_ptr_type xs) {
  return (xs != (freeitmlst_vt*)0 ? ats_true_bool : ats_false_bool) ;
}

/*
fun freeitmlst_cons {l1,l2:addr}
  (pf: freeitm_t @ l1 | x: ptr l1, xs: freeitmlst_vt l2): freeitmlst_vt l1
// end of [freeitmlst_cons]
*/

static inline
ats_ptr_type
gcats2_freeitmlst_cons
  (ats_ptr_type x, ats_ptr_type xs) { *(freeitmlst_vt*)x = xs ; return x ; }
// end of [gcats2_freeitmlst_cons]

/*
fun freeitmlst_uncons {l:anz}
  (xs: &freeitmlst_vt l >> freeitmlst_vt l_new):<> #[l_new:addr] (freeitm_t @ l | ptr l)
// end of [freeitmlst_uncons]
*/

static inline
ats_ptr_type
gcats2_freeitmlst_uncons
  (ats_ptr_type r_xs) {
  freeitmlst_vt x = *(freeitmlst_vt*)r_xs ; *(freeitmlst_vt*)r_xs = *(freeitmlst_vt*)x ;
  return x ;
} // end of [gcats2_freeitmlst_uncons]

/* ****** ****** */

static inline
topseg_t
PTR_TOPSEG_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (void*)(u >> (PTR_BOTCHKSEG_SIZE + NBYTE_PER_WORD_LOG)) ;
} /* end of [PTR_TOPSEG_GET] */

static inline
ats_int_type
PTR_BOTSEG_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (u >> (PTR_CHKSEG_SIZE + NBYTE_PER_WORD_LOG)) & BOTSEG_TABLESIZE_MASK ;
} /* end of [PTR_BOTSEG_GET] */

static inline
ats_int_type
PTR_CHKSEG_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (u >> NBYTE_PER_WORD_LOG) & CHKSEG_TABLESIZE_MASK ;
} /* end of [PTR_CHKSEG_GET] */

#if (__WORDSIZE == 64)
static inline
topseg_t
PTR_TOPSEGHASH_GET (ats_ptr_type p) {
  uintptr_t u = (uintptr_t)p ;
  return (void*)((u >> (PTR_BOTCHKSEG_SIZE + NBYTE_PER_WORD_LOG)) & TOPSEG_HASHTABLESIZE_MASK) ;
} /* end of [PTR_TOPSEGHASH_GET] */
#endif // end of ...

/* ****** ****** */

#define NMARKBIT_PER_CHUNK \
   ((CHUNK_WORDSIZE + NBIT_PER_BYTE - 1) / NBIT_PER_BYTE)

typedef
struct chunk_struct {
  // the word size of each free item: it must be positive
  int itmwsz;
  // itmwsz = 2^itmwsz_log if itmwsz_log >= 0
  // if [itmwsz_log = -1], then the chunk is large (> CHUNK_WORDSIZE)
  int itmwsz_log ;

  int itmtot ; // the total number of freeitms
  int mrkcnt ; // the count of marked freeitms

  freepageptr_vt chunk_data ; // pointer to the data // multiple of pagesize

  // bits for marking // 1 bit for 1 item (>= 1 word)
  byte mrkbits[NMARKBIT_PER_CHUNK] ;
} chunk_vt ;

typedef chunk_vt *chunkptr_vt ;
typedef chunk_vt *chunklst_vt ;

/* ****** ****** */

static inline
ats_ptr_type
gcats2_chunk_make_null () { return (void*)0 ; }

static inline
ats_void_type
gcats2_chunk_free_null (ats_ptr_type p) { return ; }

/* ****** ****** */

static inline
ats_ptr_type
gcats2_chunk_data_get
  (ats_ptr_type p_chunk) { return ((chunk_vt*)p_chunk)->chunk_data ; }
// end of ...

static inline
ats_void_type
gcats2_chunk_mrkbits_clear
  (ats_ptr_type p_chunk) {
  int itmtot ; // total number of items
  int nmrkbit ; // number of bytes for mark bits
  itmtot = ((chunk_vt*)p_chunk)->itmtot ;
  nmrkbit = (itmtot + NBIT_PER_BYTE_MASK) >> NBIT_PER_BYTE_LOG ;
/*
  fprintf(stderr, "gcats2_chunk_mrkbits_clear: itmtot = %i\n", itmtot) ;
  fprintf(stderr, "gcats2_chunk_mrkbits_clear: nmrkbit = %i\n", nmrkbit) ;
*/
  memset(((chunk_vt*)p_chunk)->mrkbits, 0, nmrkbit) ;
  ((chunk_vt*)p_chunk)->mrkcnt = 0 ;
  return ;
} /* end of [gcats2_chunk_mrkbits_clear] */

/* ****** ****** */

typedef
struct botsegtbl_struct {
#if (__WORDSIZE == 64)
  uintptr_t hashkey ; struct botsegtbl_struct *hashnext ;
#endif
  chunklst_vt headers[BOTSEG_TABLESIZE] ;
} botsegtbl_vt ;

typedef botsegtbl_vt *botsegtblptr_vt ;

/* ****** ****** */

#if (__WORDSIZE == 32)

extern botsegtbl_vt *the_topsegtbl[TOPSEG_TABLESIZE] ;

static inline
ats_ptr_type
gcats2_the_topsegtbl_takeout (topseg_t ofs) {
  return &the_topsegtbl[(uintptr_t)ofs] ; // 0 <= ofs < TOPSEG_TABLESIZE
} // end of ...

#endif // end of [__WORDSIZE == 32]

#if (__WORDSIZE == 64)

extern botsegtbl_vt *the_topsegtbl[TOPSEG_HASHTABLESIZE] ;

static inline
ats_ptr_type
gcats2_the_topsegtbl_takeout (topseg_t ofs) {
  return &the_topsegtbl[((uintptr_t)ofs) & TOPSEG_HASHTABLESIZE_MASK] ;
} // end of ...

#endif // end of [__WORDSIZE == 64]

/* ****** ****** */

#if (__WORDSIZE == 32)

static inline
ats_ptr_type // &chunkptr
gcats2_botsegtblptr1_takeout ( // used in [ptr_is_valid]
  ats_ptr_type p_botsegtbl // p_botsegtbl != 0
, topseg_t ofs_topseg, int ofs_botseg // [ofs_topseg]: not used
) {
  return &(((botsegtbl_vt*)p_botsegtbl)->headers)[ofs_botseg] ;
} /* end of [botsegtblptr_get] */

#endif // end of [__WORDSIZE == 32]

#if (__WORDSIZE == 64)

static inline
ats_ptr_type // &chunkptr
gcats2_botsegtblptr1_takeout ( // used in [ptr_is_valid]
  ats_ptr_type p_botsegtbl // p_botsegtbl != 0
, topseg_t ofs_topseg, int ofs_botseg // [ofs_topseg]: used
) {
  botsegtbl_vt *p = p_botsegtbl ;
  do {
    if (p->hashkey == (uintptr_t)ofs_topseg) return &(p->headers)[ofs_botseg] ;
    p = p->hashnext ;
  } while (p) ;
  return (chunkptr_vt*)0 ;
} /* end of [botsegtblptr_get] */

#endif // end of [__WORDSIZE == 64]

/* ****** ****** */

static inline
ats_int_type
MARK_GET (ats_ptr_type x, ats_int_type i) { return
  (((byte*)x)[i >> NBIT_PER_BYTE_LOG] >> (i & NBIT_PER_BYTE_MASK)) & 0x1 ;
} /* end of [MARK_GET] */

static inline
ats_void_type
MARK_SET (ats_ptr_type x, ats_int_type i) {
  ((byte*)x)[i >> NBIT_PER_BYTE_LOG] |= (0x1 << (i & NBIT_PER_BYTE_MASK)) ;
  return ;
} /* end of [MARK_SET] */

static inline
ats_int_type
MARK_GETSET (ats_ptr_type x, ats_int_type i) {
  byte* p_bits ; int bit ;
  p_bits = &((byte*)x)[i >> NBIT_PER_BYTE_LOG] ;
  bit = (*p_bits >> (i & NBIT_PER_BYTE_MASK)) & 0x1 ;
  if (bit) {
    return 1 ;
  } else {
    *p_bits != (0x1 << (i & NBIT_PER_BYTE_MASK)) ; return 0 ;
  } // end of [if]
} /* end of [MARK_GETSET] */

static inline
ats_bool_type
MARK_CLEAR (ats_ptr_type x, ats_int_type i) {
  ((byte*)x)[i >> NBIT_PER_BYTE_LOG] &= ~(0x1 << (i & NBIT_PER_BYTE_MASK)) ;
  return ;
} /* end of [MARK_SET] */

/* ****** ****** */

#endif /* end of [ATS_RUNTIME_GCATS2_CATS] */

/* ****** ****** */

/* end of [gcats2.cats] */
