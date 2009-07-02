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

#include <stdio.h>
// extern FILE *stdout ; // declared in [stdio.h]
// extern FILE *stderr ; // declared in [stdio.h]

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

/*
** complex numbers of single precision
*/

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_ccmplx_of_int (ats_int_type i) { return i ; }

static inline
ats_fcomplex_type
atslib_ccmplx_of_float (ats_float_type f) { return f ; }

static inline
ats_fcomplex_type
atslib_ccmplx_make_cart
  (ats_float_type r, ats_float_type i) {
  return (r + i * I) ;
}

static inline
ats_fcomplex_type
atslib_ccmplx_make_polar
  (ats_float_type r, ats_float_type t) {
  return (r * cosf(t)) + (r * sinf(t)) * I ;
}

/* ****** ****** */

extern
ats_void_type
atslib_fprint_ccmplx
  (ats_ptr_type file, ats_fcomplex_type z) ;
// end of [atslib_fprint_ccmplx]

static inline
ats_void_type
atslib_print_ccmplx (ats_fcomplex_type f) {
  atspre_stdout_view_get () ;
  atslib_fprint_ccmplx (stdout, f) ;
  atspre_stdout_view_set () ;
  return ;
} /* end of [atslib_print_ccmplx] */

static inline
ats_void_type
atslib_prerr_ccmplx (ats_fcomplex_type f) {
  atspre_stderr_view_get () ;
  atslib_fprint_ccmplx (stderr, f) ;
  atspre_stderr_view_set () ;
  return ;
} /* end of [atslib_prerr_ccmplx] */

/* ****** ****** */

static inline
ats_float_type
atslib_abs_ccmplx (ats_fcomplex_type c) { return cabsf(c) ; }

static inline
ats_fcomplex_type
atslib_neg_ccmplx (ats_fcomplex_type c) { return (-c) ; }

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_add_ccmplx_ccmplx
  (ats_fcomplex_type c1, ats_fcomplex_type c2) {
  return (c1 + c2) ;
} /* end of [atslib_add_ccmplx_ccmplx] */

static inline
ats_fcomplex_type
atslib_sub_ccmplx_ccmplx
  (ats_fcomplex_type c1, ats_fcomplex_type c2) {
  return (c1 - c2) ;
} /* end of [atslib_sub_ccmplx_ccmplx] */

static inline
ats_fcomplex_type
atslib_mul_ccmplx_ccmplx
  (ats_fcomplex_type c1, ats_fcomplex_type c2) {
  return (c1 * c2) ;
} /* end of [atslib_mul_ccmplx_ccmplx] */

static inline
ats_fcomplex_type
atslib_div_ccmplx_ccmplx
  (ats_fcomplex_type c1, ats_fcomplex_type c2) {
  return (c1 / c2) ;
} /* end of [atslib_div_ccmplx_ccmplx] */

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_sqrt_ccmplx (ats_fcomplex_type c) { return csqrtf(c) ; }

/* ****** ****** */

static inline
ats_float_type
atslib_arg_ccmplx (ats_fcomplex_type c) { return argf(c) ; }

static inline
ats_fcomplex_type
atslib_conj_ccmplx (ats_fcomplex_type c) { return conjf(c) ; }

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_exp_ccmplx (ats_fcomplex_type c) { return cexpf(c) ; }

static inline
ats_fcomplex_type
atslib_log_ccmplx (ats_fcomplex_type c) { return clogf(c) ; }

static inline
ats_fcomplex_type
atslib_pow_ccmplx_ccmplx
  (ats_fcomplex_type c1, ats_fcomplex_type c2) { return cpowf(c1, c2) ; }
/* end of [atslib_pow_ccmplx_ccmplx] */

/* ****** ****** */

/*
** complex numbers of double precision
*/

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_zcmplx_of_int (ats_int_type i) { return i ; }

static inline
ats_dcomplex_type
atslib_zcmplx_of_double (ats_double_type d) { return d ; }

static inline
ats_dcomplex_type
atslib_zcmplx_make_cart
  (ats_double_type r, ats_double_type i) {
  return (r + i * I) ;
}

static inline
ats_dcomplex_type
atslib_zcmplx_make_polar
  (ats_double_type r, ats_double_type t) {
  return (r * cos(t)) + (r * sin(t)) * I ;
}

/* ****** ****** */

extern
ats_void_type
atslib_fprint_zcmplx
  (ats_ptr_type file, ats_dcomplex_type z) ;
// end of [atslib_fprint_zcmplx]

static inline
ats_void_type
atslib_print_zcmplx (ats_dcomplex_type d) {
  atspre_stdout_view_get () ;
  atslib_fprint_zcmplx (stdout, d) ;
  atspre_stdout_view_set () ;
  return ;
} /* end of [atslib_print_zcmplx] */

static inline
ats_void_type
atslib_prerr_zcmplx (ats_dcomplex_type d) {
  atspre_stderr_view_get () ;
  atslib_fprint_zcmplx (stderr, d) ;
  atspre_stderr_view_set () ;
  return ;
} /* end of [atslib_prerr_zcmplx] */

/* ****** ****** */

static inline
ats_double_type
atslib_abs_zcmplx (ats_dcomplex_type z) { return cabs(z) ; }

static inline
ats_dcomplex_type
atslib_neg_zcmplx (ats_dcomplex_type z) { return (-z) ; }

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_add_zcmplx_zcmplx
  (ats_dcomplex_type z1, ats_dcomplex_type z2) {
  return (z1 + z2) ;
} /* end of [atslib_add_zcmplx_zcmplx] */

static inline
ats_dcomplex_type
atslib_sub_zcmplx_zcmplx
  (ats_dcomplex_type z1, ats_dcomplex_type z2) {
  return (z1 - z2) ;
} /* end of [atslib_sub_zcmplx_zcmplx] */

static inline
ats_dcomplex_type
atslib_mul_zcmplx_zcmplx
  (ats_dcomplex_type z1, ats_dcomplex_type z2) {
  return (z1 * z2) ;
} /* end of [atslib_mul_zcmplx_zcmplx] */

static inline
ats_dcomplex_type
atslib_div_zcmplx_zcmplx
  (ats_dcomplex_type z1, ats_dcomplex_type z2) {
  return (z1 / z2) ;
} /* end of [atslib_div_zcmplx_zcmplx] */

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_sqrt_zcmplx (ats_dcomplex_type z) { return csqrt(z) ; }

/* ****** ****** */

static inline
ats_double_type
atslib_arg_zcmplx (ats_dcomplex_type z) { return arg(z) ; }

static inline
ats_dcomplex_type
atslib_conj_zcmplx (ats_dcomplex_type z) { return conj(z) ; }

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_exp_zcmplx (ats_dcomplex_type z) { return cexp(z) ; }

static inline
ats_dcomplex_type
atslib_log_zcmplx (ats_dcomplex_type z) { return clog(z) ; }

static inline
ats_dcomplex_type
atslib_pow_zcmplx_zcmplx
  (ats_dcomplex_type z1, ats_dcomplex_type z2) { return cpow(z1, z2) ; }
/* end of [atslib_pow_zcmplx_zcmplx] */

/* ****** ****** */

#endif /* ATS_LIBC_COMPLEX_CATS */

/* end of [complex.cats] */
