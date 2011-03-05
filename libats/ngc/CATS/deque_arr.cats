/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
**
** ATS is  free software;  you can redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see  the  file  COPYING.  If not, write to the Free
** Software Foundation, 51  Franklin  Street,  Fifth  Floor,  Boston,  MA
** 02110-1301, USA.
*/

/* ****** ****** */

/*
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) 
**
*/

/* ****** ****** */

#ifndef ATS_LIBATS_NGC_DEQUE_ARR_CATS
#define ATS_LIBATS_NGC_DEQUE_ARR_CATS

/* ****** ****** */

typedef struct {
  ats_size_type cap ;
  ats_size_type nitm ;
  ats_ptr_type qarr_beg ;
  ats_ptr_type qarr_end ;
  ats_ptr_type qarr_fst ;
  ats_ptr_type qarr_lst ;
} atslib_ngc_deque_arr_DEQUE ;

/* ****** ****** */

#ifndef memcpy
//
// HX: [memcpy] is not a macro
//
extern
void *memcpy (void *dst, const void* src, size_t n) ;
#endif // end of [memcpy]

/* ****** ****** */
//
// HX: these two are implemented in ATS:
//
extern
ats_void_type
atslib_ngc_deque_arr_deque_initialize_tsz (
  ats_ptr_type pq
, ats_size_type qsz
, ats_ptr_type parr
, ats_size_type tsz
) ; // end of [atslib_ngc_deque_arr_deque_initialize_tsz]

extern
ats_ptr_type
atslib_ngc_deque_arr_deque_uninitialize (ats_ptr_type) ;

/* ****** ****** */

ATSinline()
ats_void_type
atslib_ngc_deque_arr_enque_many_tsz (
  ats_ptr_type q0
, ats_size_type k
, ats_ptr_type p0_xs /* buffer */
, ats_size_type tsz
) {
  atslib_ngc_deque_arr_DEQUE *q = (atslib_ngc_deque_arr_DEQUE*)q0 ;
  char *p_xs = (char*)p0_xs ;
  char *p_beg = q->qarr_beg ;
  char *p_end = q->qarr_end ;
  char *p_lst = q->qarr_lst ;
  size_t ktsz = k * tsz ;
  size_t diff = p_end - p_lst ;
  q->nitm += k ;
  if (ktsz <= diff) {
    memcpy(p_lst, p_xs, ktsz) ;
    q->qarr_lst = p_lst + ktsz ;
  } else {
    memcpy(p_lst, p_xs, diff) ;
    memcpy(p_beg, p_xs+diff, ktsz-diff) ;
    q->qarr_lst = p_beg + ktsz-diff ;
  } // end of [if]
  return ;
} // end of [atslib_ngc_deque_arr_enque_many_tsz]

/* ****** ****** */

ATSinline()
ats_void_type
atslib_ngc_deque_arr_deque_many_tsz (
  ats_ptr_type q0
, ats_size_type k
, ats_ptr_type p0_xs /* buffer */
, ats_size_type tsz
) {
  atslib_ngc_deque_arr_DEQUE *q = (atslib_ngc_deque_arr_DEQUE*)q0 ;
  char *p_xs = (char*)p0_xs ;
  char *p_beg = q->qarr_beg ;
  char *p_end = q->qarr_end ;
  char *p_fst = q->qarr_fst ;
  size_t ktsz = k * tsz ;
  size_t diff = p_end - p_fst ;
  q->nitm -= k ;
  if (ktsz <= diff) {
    memcpy(p_xs, p_fst, ktsz) ;
    q->qarr_fst = p_fst + ktsz ;
  } else {
    memcpy(p_xs, p_fst, diff) ;
    memcpy(p_xs+diff, p_beg, ktsz-diff) ;
    q->qarr_fst = p_beg + ktsz-diff ;
  } // end of [if]
  return ;
} // end of [atslib_ngc_deque_arr_deque_many_tsz]

/* ****** ****** */

ATSinline()
ats_ptr_type
atslib_ngc_deque_arr_deque_update_capacity_tsz (
  ats_ptr_type q0
, ats_size_type m2
, ats_ptr_type p0_xs /* buffer */
, ats_size_type tsz
) {
  atslib_ngc_deque_arr_DEQUE *q = (atslib_ngc_deque_arr_DEQUE*)q0 ;
  char *p_xs = (char*)p0_xs ;
  char *p_beg = q->qarr_beg ;
  char *p_end = q->qarr_end ;
  char *p_fst = q->qarr_fst ;
  size_t ntsz = q->nitm * tsz ;
  size_t diff = p_end - p_fst ;
//
  q->cap = m2 ; 
  q->qarr_beg = p_xs ;
  q->qarr_end = p_xs + m2 * tsz ;
  q->qarr_fst = p_xs ;
  q->qarr_lst = p_xs + ntsz ;
//
  if (ntsz <= diff) {
    memcpy(p_xs, p_fst, ntsz) ;
  } else {
    memcpy(p_xs, p_fst, diff) ;
    memcpy(p_xs+diff, p_beg, ntsz-diff) ;
  } // end of [if]
//
  return p_beg ;
//
} // end of [atslib_ngc_deque_arr_deque_update_capacity_tsz]

/* ****** ****** */

#endif /* ATS_LIBATS_NGC_DEQUE_ARR_CATS */

/* end of [deque_arr.cats] */ 
