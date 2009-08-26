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

static inline
ats_float_type
atslib_crealf (ats_fcomplex_type c) { return crealf(c) ; }

static inline
ats_float_type
atslib_cimagf (ats_fcomplex_type c) { return cimagf(c) ; }

/* ****** ****** */

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
ats_bool_type
atslib_eq_ccmplx_ccmplx
  (ats_fcomplex_type c1, ats_fcomplex_type c2) {
  return (c1 == c2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atslib_eq_ccmplx_ccmplx] */

static inline
ats_bool_type
atslib_neq_ccmplx_ccmplx
  (ats_fcomplex_type c1, ats_fcomplex_type c2) {
  return (c1 != c2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atslib_neq_ccmplx_ccmplx] */

/* ****** ****** */

static inline
ats_float_type
atslib_cabsf (ats_fcomplex_type c) { return cabsf(c) ; }

static inline
ats_fcomplex_type
atslib_csqrtf (ats_fcomplex_type c) { return csqrtf(c) ; }

/* ****** ****** */

static inline
ats_float_type
atslib_cargf (ats_fcomplex_type c) { return cargf(c) ; }

static inline
ats_fcomplex_type
atslib_conjf (ats_fcomplex_type c) { return conjf(c) ; }

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_csinf (ats_fcomplex_type c) { return csinf(c) ; }

static inline
ats_fcomplex_type
atslib_ccosf (ats_fcomplex_type c) { return ccosf(c) ; }

static inline
ats_fcomplex_type
atslib_ctanf (ats_fcomplex_type c) { return ctanf(c) ; }

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_casinf (ats_fcomplex_type c) { return casinf(c) ; }

static inline
ats_fcomplex_type
atslib_cacosf (ats_fcomplex_type c) { return cacosf(c) ; }

static inline
ats_fcomplex_type
atslib_catanf (ats_fcomplex_type c) { return catanf(c) ; }

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_csinhf (ats_fcomplex_type c) { return csinhf(c) ; }

static inline
ats_fcomplex_type
atslib_ccoshf (ats_fcomplex_type c) { return ccoshf(c) ; }

static inline
ats_fcomplex_type
atslib_ctanhf (ats_fcomplex_type c) { return ctanhf(c) ; }

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_casinhf (ats_fcomplex_type c) { return casinhf(c) ; }

static inline
ats_fcomplex_type
atslib_cacoshf (ats_fcomplex_type c) { return cacoshf(c) ; }

static inline
ats_fcomplex_type
atslib_catanhf (ats_fcomplex_type c) { return catanhf(c) ; }

/* ****** ****** */

static inline
ats_fcomplex_type
atslib_cexpf (ats_fcomplex_type c) { return cexpf(c) ; }

static inline
ats_fcomplex_type
atslib_clogf (ats_fcomplex_type c) { return clogf(c) ; }

static inline
ats_fcomplex_type
atslib_cpowf (
  ats_fcomplex_type c1
, ats_fcomplex_type c2
) {
  return cpowf(c1, c2) ;
} /* end of [atslib_cpowf] */

/* ****** ****** */

static inline
ats_float_type
atslib_cprojf (ats_fcomplex_type c) { return cprojf(c) ; }

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

static inline
ats_double_type
atslib_creal (ats_dcomplex_type z) { return creal(z) ; }

static inline
ats_double_type
atslib_cimag (ats_dcomplex_type z) { return cimag(z) ; }

/* ****** ****** */

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
ats_bool_type
atslib_eq_zcmplx_zcmplx
  (ats_dcomplex_type c1, ats_dcomplex_type c2) {
  return (c1 == c2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atslib_eq_zcmplx_zcmplx] */

static inline
ats_bool_type
atslib_neq_zcmplx_zcmplx
  (ats_dcomplex_type c1, ats_dcomplex_type c2) {
  return (c1 != c2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atslib_neq_zcmplx_zcmplx] */

/* ****** ****** */

static inline
ats_double_type
atslib_cabs (ats_dcomplex_type z) { return cabs(z) ; }

static inline
ats_dcomplex_type
atslib_csqrt (ats_dcomplex_type z) { return csqrt(z) ; }

/* ****** ****** */

static inline
ats_double_type
atslib_carg (ats_dcomplex_type z) { return carg(z) ; }

static inline
ats_dcomplex_type
atslib_conj (ats_dcomplex_type z) { return conj(z) ; }

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_csin (ats_dcomplex_type z) { return csin(z) ; }

static inline
ats_dcomplex_type
atslib_ccos (ats_dcomplex_type z) { return ccos(z) ; }

static inline
ats_dcomplex_type
atslib_ctan (ats_dcomplex_type z) { return ctan(z) ; }

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_casin (ats_dcomplex_type z) { return casin(z) ; }

static inline
ats_dcomplex_type
atslib_cacos (ats_dcomplex_type z) { return cacos(z) ; }

static inline
ats_dcomplex_type
atslib_catan (ats_dcomplex_type z) { return catan(z) ; }

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_csinh (ats_dcomplex_type z) { return csinh(z) ; }

static inline
ats_dcomplex_type
atslib_ccosh (ats_dcomplex_type z) { return ccosh(z) ; }

static inline
ats_dcomplex_type
atslib_ctanh (ats_dcomplex_type z) { return ctanh(z) ; }

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_casinh (ats_dcomplex_type z) { return casinh(z) ; }

static inline
ats_dcomplex_type
atslib_cacosh (ats_dcomplex_type z) { return cacosh(z) ; }

static inline
ats_dcomplex_type
atslib_catanh (ats_dcomplex_type z) { return catanh(z) ; }

/* ****** ****** */

static inline
ats_dcomplex_type
atslib_cexp (ats_dcomplex_type z) { return cexp(z) ; }

static inline
ats_dcomplex_type
atslib_clog (ats_dcomplex_type z) { return clog(z) ; }

static inline
ats_dcomplex_type
atslib_cpow (
  ats_dcomplex_type z1
, ats_dcomplex_type z2
) {
  return cpow(z1, z2) ;
} /* end of [atslib_cpow] */

/* ****** ****** */

static inline
ats_double_type
atslib_cproj (ats_dcomplex_type z) { return cproj(z) ; }

/* ****** ****** */

#endif /* ATS_LIBC_COMPLEX_CATS */

/* end of [complex.cats] */
