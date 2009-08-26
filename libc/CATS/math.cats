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

#ifndef ATS_LIBC_MATH_CATS
#define ATS_LIBC_MATH_CATS

/* ****** ****** */

#include <math.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

// some of these functions may not be declared in [math.h]

extern double ceil (double x) ;
extern float ceilf (float x) ;
extern long double ceill (long double x) ;

extern double floor (double x) ;
extern float floorf (float x) ;
extern long double floorl (long double x) ;

extern double round (double x) ;
extern float roundf (float x) ;
extern long double roundl (long double x) ;

extern double trunc (double x) ;
extern float truncf (float x) ;
extern long double truncl (long double x) ;

extern double fmod (double x, double y) ;
extern float fmodf (float x, float y) ;
extern long double fmodl (long double x, long double y) ;

extern double sqrt (double x) ;
extern float sqrtf (float x) ;
extern long double sqrtl (long double x) ;

extern double cbrt (double x) ;
extern float cbrtf (float x) ;
extern long double cbrtl (long double x) ;

extern double pow (double x, double y) ;
extern float powf (float x, float y) ;
extern long double powl (long double x, long double y) ;

extern double exp (double x) ;
extern float expf (float x) ;
extern long double expl (long double x) ;

extern double log (double x) ;
extern float logf (float x) ;
extern long double logl (long double x) ;

extern double asin (double x) ;
extern float asinf (float x) ;
extern long double asinl (long double x) ;

extern double acos (double x) ;
extern float acosf (float x) ;
extern long double acosl (long double x) ;

extern double atan (double x) ;
extern float atanf (float x) ;
extern long double atanl (long double x) ;

extern double atan2 (double x, double y) ;
extern float atan2f (float x, float y) ;
extern long double atan2l (long double x, long double y) ;

extern double asinh (double x) ;
extern float asinhf (float x) ;
extern long double asinhl (long double x) ;

extern double acosh (double x) ;
extern float acoshf (float x) ;
extern long double acoshl (long double x) ;

extern double sin (double x) ;
extern float sinf (float x) ;
extern long double sinl (long double x) ;

extern double cos (double x) ;
extern float cosf (float x) ;
extern long double cosl (long double x) ;

extern double tan (double x) ;
extern float tanf (float x) ;
extern long double tanl (long double x) ;

/* ****** ****** */

static inline
ats_double_type
atslib_ceil(ats_double_type x) { return ceil(x) ; }

static inline
ats_float_type
atslib_ceilf(ats_float_type x) { return ceilf(x) ; }

static inline
ats_ldouble_type
atslib_ceill(ats_ldouble_type x) {
  return ceill(x) ;
}

//

static inline
ats_double_type
atslib_floor(ats_double_type x) { return floor(x) ; }

static inline
ats_float_type
atslib_floorf(ats_float_type x) { return floorf(x) ; }

static inline
ats_ldouble_type
atslib_floorl(ats_ldouble_type x) { return floorl(x) ; }

//

static inline
ats_double_type
atslib_round(ats_double_type x) { return round(x) ; }

static inline
ats_float_type
atslib_roundf(ats_float_type x) { return roundf(x) ; }

static inline
ats_ldouble_type
atslib_roundl(ats_ldouble_type x) { return roundl(x) ; }

//

static inline
ats_double_type
atslib_trunc(ats_double_type x) { return trunc(x) ; }

static inline
ats_float_type
atslib_truncf(ats_float_type x) { return truncf(x) ; }

static inline
ats_ldouble_type
atslib_truncl(ats_ldouble_type x) { return truncl(x) ; }

//

static inline
ats_double_type
atslib_fmod (ats_double_type f1, ats_double_type f2) {
  return fmod(f1, f2) ;
}

static inline
ats_float_type
atslib_fmodf (ats_float_type f1, ats_float_type f2) {
  return fmodf(f1, f2) ;
}

static inline
ats_ldouble_type
atslib_fmodl (ats_ldouble_type f1, ats_ldouble_type f2) {
  return fmodl(f1, f2) ;
}

/* ****** ****** */

static inline
ats_double_type
atslib_sqrt (ats_double_type f) {
  return sqrt(f) ;
}

static inline
ats_float_type
atslib_sqrtf (ats_float_type f) {
  return sqrtf(f) ;
}

static inline
ats_ldouble_type
atslib_sqrtl (ats_ldouble_type f) {
  return sqrtl(f) ;
}

//

static inline
ats_double_type
atslib_cbrt (ats_double_type f) {
  return cbrt(f) ;
}

static inline
ats_float_type
atslib_cbrtf (ats_float_type f) {
  return cbrtf(f) ;
}

static inline
ats_ldouble_type
atslib_cbrtl (ats_ldouble_type f) {
  return cbrtl(f) ;
}

//

static inline
ats_double_type
atslib_pow (ats_double_type f1, ats_double_type f2) {
  return pow(f1, f2) ;
}

static inline
ats_float_type
atslib_powf (ats_float_type f1, ats_float_type f2) {
  return powf(f1, f2) ;
}

static inline
ats_ldouble_type
atslib_powl (ats_ldouble_type f1, ats_ldouble_type f2) {
  return powl(f1, f2) ;
}

/* ****** ****** */

static inline
ats_double_type
atslib_exp(ats_double_type x) { return exp(x) ; }

static inline
ats_float_type
atslib_expf(ats_float_type x) { return expf(x) ; }

static inline
ats_ldouble_type
atslib_expl(ats_ldouble_type x) { return expl(x) ; }

/* ****** ****** */

static inline
ats_double_type
atslib_log(ats_double_type x) { return log(x) ; }

static inline
ats_float_type
atslib_logf(ats_float_type x) { return logf(x) ; }

static inline
ats_ldouble_type
atslib_logl(ats_ldouble_type x) { return logl(x) ; }

/* ****** ****** */

static inline
ats_double_type
atslib_asin(ats_double_type x) { return asin(x) ; }

static inline
ats_float_type
atslib_asinf(ats_float_type x) { return asinf(x) ; }

static inline
ats_ldouble_type
atslib_asinl(ats_ldouble_type x) {
  return asinl(x) ;
}

static inline
ats_double_type
atslib_acos(ats_double_type x) { return acos(x) ; }

static inline
ats_float_type
atslib_acosf(ats_float_type x) { return acosf(x) ; }

static inline
ats_ldouble_type
atslib_acosl(ats_ldouble_type x) {
  return acosl(x) ;
}

static inline
ats_double_type
atslib_atan(ats_double_type x) { return atan(x) ; }

static inline
ats_float_type
atslib_atanf(ats_float_type x) { return atanf(x) ; }

static inline
ats_ldouble_type
atslib_atanl(ats_ldouble_type x) { return atanl(x) ; }

static inline
ats_double_type
atslib_atan2(ats_double_type x, ats_double_type y) {
  return atan2(x, y) ;
}

static inline
ats_float_type
atslib_atan2f(ats_float_type x, ats_float_type y) {
  return atan2(x, y) ;
}

static inline
ats_ldouble_type
atslib_atan2l(ats_ldouble_type x, ats_ldouble_type y) {
  return atan2l(x, y) ;
}

//

static inline
ats_double_type
atslib_asinh(ats_double_type x) { return asinh(x) ; }

static inline
ats_float_type
atslib_asinhf(ats_float_type x) { return asinhf(x) ; }

static inline
ats_ldouble_type
atslib_asinhl(ats_ldouble_type x) {
  return asinhl(x) ;
}

static inline
ats_double_type
atslib_acosh(ats_double_type x) { return acosh(x) ; }

static inline
ats_float_type
atslib_acoshf(ats_float_type x) { return acoshf(x) ; }

static inline
ats_ldouble_type
atslib_acoshl(ats_ldouble_type x) {
  return acoshl(x) ;
}

//

static inline
ats_double_type
atslib_sin(ats_double_type x) { return sin(x) ; }

static inline
ats_float_type
atslib_sinf(ats_float_type x) { return sinf(x) ; }

static inline
ats_ldouble_type
atslib_sinl(ats_ldouble_type x) { return sinl(x) ; }

//

static inline
ats_double_type
atslib_cos(ats_double_type x) { return cos(x) ; }

static inline
ats_float_type
atslib_cosf(ats_float_type x) { return cosf(x) ; }

static inline
ats_ldouble_type
atslib_cosl(ats_ldouble_type x) { return cosl(x) ; }

//

static inline
ats_double_type
atslib_tan(ats_double_type x) { return tan(x) ; }

static inline
ats_float_type
atslib_tanf(ats_float_type x) { return tanf(x) ; }

static inline
ats_ldouble_type
atslib_tanl(ats_ldouble_type x) { return tanl(x) ; }

/* ****** ****** */

static inline
ats_int_type
atslib_isinf (ats_double_type x) { return isinf(x) ; } 

static inline
ats_int_type
atslib_isnan (ats_double_type x) { return isnan(x) ; } 

/* ****** ****** */

#endif /* ATS_LIBC_MATH_CATS */

/* end of [math.cats] */
