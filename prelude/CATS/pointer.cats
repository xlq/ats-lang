/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi.
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
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
 *
 */

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATS_PRELUDE_POINTER_CATS
#define ATS_PRELUDE_POINTER_CATS

/* ****** ****** */

#include <stdio.h> // for [fprintf]
#include <string.h> // for [memcpy]

/* ****** ****** */

#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

static
ats_ptr_type atspre_null_ptr = (ats_ptr_type)0 ;

static inline
ats_bool_type
atspre_ptr_is_null (ats_ptr_type p) {
  return (p == (ats_ptr_type)0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
atspre_ptr_is_not_null (ats_ptr_type p) {
  return (p != (ats_ptr_type)0 ? ats_true_bool : ats_false_bool) ;
}

/* ****** ****** */

static inline
ats_ptr_type
atspre_psucc (const ats_ptr_type p) {
  return ((ats_byte_type*)p) + 1 ;
}

static inline
ats_ptr_type
atspre_ppred (const ats_ptr_type p) {
  return ((ats_byte_type*)p) - 1 ;
}

/* ****** ****** */

static inline
ats_ptr_type
atspre_padd (const ats_ptr_type p, const ats_int_type n) {
  return ((ats_byte_type*)p) + n ;
}

static inline
ats_ptr_type
atspre_psub (const ats_ptr_type p, const ats_int_type n) {
  return ((ats_byte_type*)p) - n ;
}

static inline
ats_int_type
atspre_pdiff (const ats_ptr_type p1, const ats_ptr_type p2) {
  return ((ats_byte_type*)p1 - (ats_byte_type*)p2) ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_plt (const ats_ptr_type p1, const ats_ptr_type p2) {
  return (p1 < p2) ;
}

static inline
ats_bool_type
atspre_plte (const ats_ptr_type p1, const ats_ptr_type p2) {
  return (p1 <= p2) ;
}

static inline
ats_bool_type
atspre_pgt (const ats_ptr_type p1, const ats_ptr_type p2) {
  return (p1 > p2) ;
}

static inline
ats_bool_type
atspre_pgte (const ats_ptr_type p1, const ats_ptr_type p2) {
  return (p1 >= p2) ;
}

static inline
ats_bool_type
atspre_peq (const ats_ptr_type p1, const ats_ptr_type p2) {
  return (p1 == p2) ;
}

static inline
ats_bool_type
atspre_pneq (const ats_ptr_type p1, const ats_ptr_type p2) {
  return (p1 != p2) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_ptr (const ats_ptr_type out, const ats_ptr_type p) {
  int n = fprintf ((FILE *)out, "%p", p) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_pointer] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_ptr(const ats_ptr_type p) {
  atspre_stdout_view_get() ;
  fprintf (stdout, "%p", p) ;
  atspre_stdout_view_set() ;
  return ;
}

static inline
ats_void_type
atspre_prerr_ptr(const ats_ptr_type p) {
  atspre_stderr_view_get() ;
  fprintf (stderr, "%p", p) ;
  atspre_stderr_view_set() ;
  return ;
}

/* ****** ****** */

static inline
ats_ptr_type
atspre_ptr_alloc_tsz(const ats_int_type tsz) {
  ats_ptr_type p ;
  p = ATS_MALLOC(tsz) ; return p ;
}

static inline
ats_void_type
atspre_ptr_free(const ats_ptr_type ptr) {
  ATS_FREE(ptr) ; return ;
}

/* ****** ****** */

// for both [ptr_move_t_tsz] and [ptr_move_vt_tsz]

static inline
ats_void_type
atspre_ptr_move_tsz
  (ats_ptr_type p1, ats_ptr_type p2, ats_int_type tsz) {
  memcpy (p2, p1, (size_t)tsz) ; return ;
}

/* ****** ****** */

#endif /* ATS_PRELUDE_POINTER_CATS */

/* end of [pointer.cats] */
