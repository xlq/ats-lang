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
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATS_LIBC_COMPLEX_CATS
#define ATS_LIBC_COMPLEX_CATS

/* ****** ****** */

#include <complex.h>
#include <math.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

typedef float complex ats_fcomplex_type ;
typedef double complex ats_dcomplex_type ;
typedef long double complex ats_lcomplex_type ;

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_ccmplx_of_int (ats_int_type i) { return i ; }

static inline
ats_dcomplex_type
atslib_ccmplx_of_double (ats_double_type f) { return f ; }

static inline
ats_dcomplex_type
atslib_ccmplx_make_cart
  (ats_double_type r, ats_double_type i) {
  return (r + i * I) ;
}

static inline
ats_dcomplex_type
atslib_ccmplx_make_polar
  (ats_double_type r, ats_double_type t) {
  return (r * cos(t)) + (r * sin(t)) * I ;
}

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_conj_ccmplx (ats_dcomplex_type c) { return conj(c) ; }

static inline
ats_dcomplex_type
atslib_sqrt_ccmplx (ats_dcomplex_type c) { return csqrt(c) ; }

static inline
ats_dcomplex_type
atslib_exp_ccmplx (ats_dcomplex_type c) { return cexp(c) ; }

/* ****** ****** */

#include <stdio.h>
// extern FILE *stdout ; // declared in [stdio.h]
// extern FILE *stderr ; // declared in [stdio.h]

extern
ats_void_type
atslib_fprint_ccmplx
  (ats_ptr_type file, ats_dcomplex_type c) ;
// end of [atslib_fprint_ccmplx]

static inline
ats_void_type
atslib_print_ccmplx (ats_dcomplex_type f) {
  atspre_stdout_view_get () ;
  atslib_fprint_ccmplx (stdout, f) ;
  atspre_stdout_view_set () ;
  return ;
} /* end of [atslib_print_ccmplx] */

static inline
ats_void_type
atslib_prerr_ccmplx (ats_dcomplex_type f) {
  atspre_stderr_view_get () ;
  atslib_fprint_ccmplx (stderr, f) ;
  atspre_stderr_view_set () ;
  return ;
} /* end of [atslib_prerr_ccmplx] */

/* ****** ****** */

#endif /* ATS_LIBC_COMPLEX_CATS */

/* end of [complex.cats] */
