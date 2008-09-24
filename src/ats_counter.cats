/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi.
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 */

/* ****** ****** */

// July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

/* ****** ****** */

/* ats_counter: a simple counter implementation */

/* ****** ****** */

#ifndef ATS_SRC_COUNTER_CATS
#define ATS_SRC_COUNTER_CATS

/* ****** ****** */

#include <stdio.h>

/* ****** ****** */

#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

typedef ats_int64_type ats_counter_count_type ;
typedef ats_counter_count_type *ats_counter_counter_type ;

static inline
ats_counter_counter_type
ats_counter_counter_make () {
  ats_counter_counter_type cntr ;
  cntr = ATS_MALLOC (sizeof(ats_counter_count_type)) ;
  *cntr = 0 ; return cntr ;
}

static inline
ats_void_type
ats_counter_counter_inc (ats_counter_counter_type cntr) {
  *cntr += 1 ; return ;
}

static inline
ats_counter_count_type
ats_counter_counter_get (ats_counter_counter_type cntr) {
  return *cntr ;
}

static inline
ats_void_type
ats_counter_counter_set
  (ats_counter_counter_type cntr, ats_counter_count_type cnt)
{
 *cntr = cnt ; return ;
}

static inline
ats_void_type
ats_counter_counter_reset (ats_counter_counter_type cntr) {
 *cntr = 0 ; return ;
}

static inline
ats_counter_count_type
ats_counter_counter_get_and_inc (ats_counter_counter_type cntr) { 
  ats_counter_count_type cnt ;
  cnt = *cntr ; *cntr += 1 ; return cnt ;
}

static inline
ats_counter_count_type
ats_counter_counter_inc_and_get (ats_counter_counter_type cntr)
{ 
  *((ats_counter_count_type*)cntr) += 1 ;
  return *cntr ;
}

/* ****** ****** */

static inline
ats_int_type
ats_counter_compare_count_count
  (ats_counter_count_type cnt1, ats_counter_count_type cnt2) {
  if (cnt1 < cnt2) return -1 ;
  if (cnt1 > cnt2) return  1 ;
  return 0 ;
}

/* ****** ****** */

static inline
ats_uint_type
ats_counter_count_hash (ats_counter_count_type cnt) {
  /* 2654435761 is the golden ration of 2^32 */
  return (2654435761UL * (ats_uint_type)cnt) ;
}

/* ****** ****** */

static inline
ats_void_type
ats_counter_fprint_count
  (ats_ptr_type out, ats_counter_count_type cnt) {
  fprintf ((FILE*)out, "%lli", cnt) ; return ;
}

/* ****** ****** */

extern ats_ptr_type atspre_tostringf (ats_ptr_type format, ...) ;

static inline
ats_ptr_type
ats_counter_tostring_count (ats_counter_count_type cnt) {
  return atspre_tostringf ("%lli", cnt) ;
}

static inline
ats_ptr_type
ats_counter_tostring_count_prefix
  (ats_ptr_type pre, ats_counter_count_type cnt) {
  return atspre_tostringf ("%s%lli", (char *)pre, cnt) ;
}

/* ****** ****** */

#endif // ATS_SRC_COUNTER_CATS

/* end of [ats_counter.cats] */
