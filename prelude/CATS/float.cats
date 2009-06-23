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
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
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

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATS_PRELUDE_FLOAT_CATS
#define ATS_PRELUDE_FLOAT_CATS

/* ****** ****** */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "ats_types.h"

/* ****** ****** */

extern
ats_ptr_type atspre_tostringf (ats_ptr_type fmt, ...) ;

/* ****** ****** */

/* floating point numbers of single precision */

/* ****** ****** */

static inline
ats_int_type
atspre_int_of_float (ats_float_type f) { return f ; }

static inline
ats_lint_type
atspre_lint_of_float (ats_float_type f) { return f ; }

static inline
ats_llint_type
atspre_llint_of_float (ats_float_type f) { return f ; }

//

static inline
ats_float_type
atspre_float_of_int (const ats_int_type i) {
  return (ats_float_type)i ;
}

static inline
ats_float_type
atspre_float_of_lint (const ats_lint_type li) {
  return (ats_float_type)li ;
}

static inline
ats_float_type
atspre_float_of_llint (const ats_llint_type lli) {
  return (ats_float_type)lli ;
}

//

static inline
ats_float_type
atspre_float_of_double (const ats_double_type d) {
  return (ats_float_type)d ;
}

static inline
ats_float_type
atspre_float_of_string (const ats_ptr_type s) {
  return (ats_float_type)(atof ((char *)s)) ;
}

//

static inline
ats_float_type
atspre_abs_float (const ats_float_type f) {
  return (f >= 0.0 ? f : -f) ;
}

static inline
ats_float_type
atspre_neg_float (const ats_float_type f) {
  return (-f) ;
}

static inline
ats_float_type
atspre_succ_float (const ats_float_type f) {
  return (f + 1.0) ;
}

static inline
ats_float_type
atspre_pred_float (const ats_float_type f) {
  return (f - 1.0) ;
}

static inline
ats_float_type
atspre_add_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 + f2) ;
}

static inline
ats_float_type
atspre_sub_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 - f2) ;
}

//

static inline
ats_float_type
atspre_mul_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 * f2) ;
}

static inline
ats_float_type
atspre_mul_int_float
  (const ats_int_type i1, const ats_float_type f2) {
  return ((float)i1 * f2) ;
}

//

static inline
ats_float_type
atspre_div_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 / f2) ;
}

static inline
ats_float_type
atspre_div_float_int
  (const ats_float_type f1, const ats_int_type i2) {
  return (f1 / (float)i2) ;
}

//

static inline
ats_bool_type
atspre_lt_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 < f2) ;
}

static inline
ats_bool_type
atspre_lte_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 <= f2) ;
}

static inline
ats_bool_type
atspre_gt_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 > f2) ;
}

static inline
ats_bool_type
atspre_gte_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 >= f2) ;
}

static inline
ats_bool_type
atspre_eq_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 == f2) ;
}

static inline
ats_bool_type
atspre_neq_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 != f2) ;
}

// compare, max and min

static inline
ats_int_type
atspre_compare_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  if (f1 < f2) return (-1) ;
  if (f1 > f2) return ( 1) ;
  return 0 ;
}

static inline
ats_float_type
atspre_max_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 >= f2) ? f1 : f2 ;
}

static inline
ats_float_type
atspre_min_float_float
  (const ats_float_type f1, const ats_float_type f2) {
  return (f1 <= f2) ? f1 : f2 ;
}

// square function

static inline
ats_float_type
atspre_square_float (const ats_float_type f) {
  return (f * f) ;
}

// print function

static inline
ats_void_type
atspre_fprint_float (
  const ats_ptr_type out, const ats_float_type f
) {
  int n = fprintf ((FILE *)out, "%f", f) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_float] failed.\n") ;
  }
  return ;
} /* end of [atspre_fprint_float] */

static inline
ats_void_type
atspre_print_float (const ats_float_type f) {
  atspre_stdout_view_get () ;
  atspre_fprint_float (stdout, f) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_float (const ats_float_type f) {
  atspre_stderr_view_get () ;
  atspre_fprint_float (stderr, f) ;
  atspre_stderr_view_set () ;
  return ;
}

// stringization

static inline
ats_ptr_type
atspre_tostring_float (const ats_float_type f) {
  return atspre_tostringf ("%f", f) ;
}

/* ****** ****** */

/* floating point numbers of double precision */

/* ****** ****** */

static inline
ats_int_type
atspre_int_of_double (ats_double_type d) { return d ; }

static inline
ats_lint_type
atspre_lint_of_double (ats_double_type d) { return d ; }

static inline
ats_llint_type
atspre_llint_of_double (ats_double_type d) { return d ; }

//

static inline
ats_double_type
atspre_double_of_int (const ats_int_type i) {
  return (ats_double_type)i ;
}

static inline
ats_double_type
atspre_double_of_lint (const ats_lint_type li) {
  return (ats_double_type)li ;
}

static inline
ats_double_type
atspre_double_of_llint (const ats_llint_type lli) {
  return (ats_double_type)lli ;
}

//

static inline
ats_double_type
atspre_double_of_float (const ats_float_type f) {
  return (ats_double_type)f ;
}

static inline
ats_double_type
atspre_double_of_string (const ats_ptr_type s) {
  return (ats_double_type)(atof ((char *)s)) ;
}

//

static inline
ats_double_type
atspre_abs_double (const ats_double_type f) {
  return (f >= 0.0 ? f : -f) ;
}

static inline
ats_double_type
atspre_neg_double (const ats_double_type f) {
  return (-f) ;
}

static inline
ats_double_type
atspre_succ_double (const ats_double_type f) {
  return (f + 1.0) ;
}

static inline
ats_double_type
atspre_pred_double (const ats_double_type f) {
  return (f - 1.0) ;
}

//

static inline
ats_double_type
atspre_add_double_double
  (const ats_double_type f1, const ats_double_type f2) {
  return (f1 + f2) ;
}

static inline
ats_double_type
atspre_add_double_int
  (const ats_double_type f1, const ats_int_type i2) {
  return (f1 + i2) ;
}

static inline
ats_double_type
atspre_add_int_double
  (const ats_int_type i1, const ats_double_type f2) {
  return (i1 + f2) ;
}

//

static inline
ats_double_type
atspre_sub_double_double
  (const ats_double_type f1, const ats_double_type f2) {
  return (f1 - f2) ;
}

static inline
ats_double_type
atspre_sub_double_int
  (const ats_double_type f1, const ats_int_type i2) {
  return (f1 - i2) ;
}

static inline
ats_double_type
atspre_sub_int_double
  (const ats_double_type i1, const ats_int_type f2) {
  return (i1 - f2) ;
}

//

static inline
ats_double_type
atspre_mul_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 * d2) ;
}

static inline
ats_double_type
atspre_mul_double_int
  (const ats_double_type d1, const ats_int_type i2) {
  return (d1 * (double)i2) ;
}

static inline
ats_double_type
atspre_mul_int_double
  (const ats_int_type i1, const ats_double_type d2) {
  return ((double)i1 * d2) ;
}

//

static inline
ats_double_type
atspre_div_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 / d2) ;
}

static inline
ats_double_type
atspre_div_double_int
  (const ats_double_type d1, const ats_int_type i2) {
  return (d1 / (double)i2) ;
}

static inline
ats_double_type
atspre_div_int_double
  (const ats_int_type i1, const ats_double_type d2) {
  return ((double)i1 / d2) ;
}

//

static inline
ats_bool_type
atspre_lt_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 < d2) ;
}

static inline
ats_bool_type
atspre_lte_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 <= d2) ;
}

static inline
ats_bool_type
atspre_gt_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 > d2) ;
}

static inline
ats_bool_type
atspre_gte_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 >= d2) ;
}

static inline
ats_bool_type
atspre_eq_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 == d2) ;
}

static inline
ats_bool_type
atspre_neq_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 != d2) ;
}

// compare, max and min

static inline
ats_int_type
atspre_compare_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  if (d1 < d2) return (-1) ;
  else if (d1 > d2) return ( 1) ;
  else return 0 ;
}

static inline
ats_double_type
atspre_max_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 >= d2) ? d1 : d2 ;
}

static inline
ats_double_type
atspre_min_double_double
  (const ats_double_type d1, const ats_double_type d2) {
  return (d1 <= d2) ? d1 : d2 ;
}

// square function

static inline
ats_double_type
atspre_square_double (const ats_double_type d) {
  return (d * d) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_double
  (const ats_ptr_type out, const ats_double_type f) {
  int n = fprintf ((FILE *)out, "%f", f) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_double] failed.\n") ;
  }
  return ;
} /* end of [atspre_fprint_double] */

static inline
ats_void_type
atspre_print_double (const ats_double_type f) {
  atspre_stdout_view_get () ;
  atspre_fprint_double (stdout, f) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_double (const ats_double_type f) {
  atspre_stderr_view_get () ;
  atspre_fprint_double (stderr, f) ;
  atspre_stderr_view_set () ;
  return ;
}

// stringization

static inline
ats_ptr_type
atspre_tostring_double (const ats_double_type f) {
  return atspre_tostringf ("%f", f) ;
}

/* ****** ****** */

/* floating point numbers of long double precision */

/* ****** ****** */

static inline
ats_int_type
atspre_int_of_ldouble (ats_ldouble_type ld) { return ld ; }

static inline
ats_lint_type
atspre_lint_of_ldouble (ats_ldouble_type ld) { return ld ; }

static inline
ats_llint_type
atspre_llint_of_ldouble (ats_ldouble_type ld) { return ld ; }

//

static inline
ats_ldouble_type
atspre_ldouble_of_int (const ats_int_type i) {
  return ((ats_ldouble_type)i) ;
}

static inline
ats_ldouble_type
atspre_ldouble_of_lint (const ats_lint_type li) {
  return (ats_ldouble_type)li ;
}

static inline
ats_ldouble_type
atspre_ldouble_of_llint (const ats_llint_type lli) {
  return (ats_ldouble_type)lli ;
}

//

static inline
ats_ldouble_type
atspre_ldouble_of_float (const ats_float_type f) {
  return ((ats_ldouble_type)f) ;
}

static inline
ats_ldouble_type
atspre_ldouble_of_double (const ats_double_type d) {
  return ((ats_ldouble_type)d) ;
}

//

static inline
ats_ldouble_type
atspre_abs_ldouble (const ats_ldouble_type f) {
  return (f >= 0.0 ? f : -f) ;
}

static inline
ats_ldouble_type
atspre_neg_ldouble (const ats_ldouble_type f) {
  return (-f) ;
}

static inline
ats_ldouble_type
atspre_succ_ldouble (const ats_ldouble_type f) {
  return (f + 1.0) ;
}

static inline
ats_ldouble_type
atspre_pred_ldouble (const ats_ldouble_type f) {
  return (f - 1.0) ;
}

static inline
ats_ldouble_type
atspre_add_ldouble_ldouble
  (const ats_ldouble_type f1, const ats_ldouble_type f2) {
  return (f1 + f2) ;
}

static inline
ats_ldouble_type
atspre_sub_ldouble_ldouble
  (const ats_ldouble_type f1, const ats_ldouble_type f2) {
  return (f1 - f2) ;
}

//

static inline
ats_ldouble_type
atspre_mul_ldouble_ldouble
  (const ats_ldouble_type f1, const ats_ldouble_type f2) {
  return (f1 * f2) ;
}

static inline
ats_ldouble_type
atspre_mul_int_ldouble
  (const ats_int_type i1, const ats_ldouble_type ld2) {
  return ((long double)i1 * ld2) ;
}

//

static inline
ats_ldouble_type
atspre_div_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 / ld2) ;
}

static inline
ats_ldouble_type
atspre_div_ldouble_int
  (const ats_ldouble_type ld1, const ats_int_type i2) {
  return (ld1 / (long double)i2) ;
}

//

static inline
ats_bool_type
atspre_lt_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 == ld2) ;
}

static inline
ats_bool_type
atspre_lte_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 <= ld2) ;
}

static inline
ats_bool_type
atspre_gt_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 > ld2) ;
}

static inline
ats_bool_type
atspre_gte_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 >= ld2) ;
}

static inline
ats_bool_type
atspre_eq_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 == ld2) ;
}

static inline
ats_bool_type
atspre_neq_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 != ld2) ;
}

// compare, max and min

static inline
ats_int_type
atspre_compare_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  if (ld1 < ld2) return (-1) ;
  else if (ld1 > ld2) return ( 1) ;
  else return 0 ;
}

static inline
ats_ldouble_type
atspre_max_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 >= ld2) ? ld1 : ld2 ;
}

static inline
ats_ldouble_type
atspre_min_ldouble_ldouble
  (const ats_ldouble_type ld1, const ats_ldouble_type ld2) {
  return (ld1 <= ld2) ? ld1 : ld2 ;
}

// square function

static inline
ats_ldouble_type
atspre_square_ldouble (const ats_ldouble_type ld) {
  return (ld * ld) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_ldouble
  (const ats_ptr_type out, const ats_ldouble_type f) {
  int n = fprintf ((FILE *)out, "%Lf", f) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_ldouble] failed.\n") ;
  }
  return ;
} /* end of [atspre_fprint_ldouble] */

static inline
ats_void_type
atspre_print_ldouble (const ats_ldouble_type f) {
  atspre_stdout_view_get () ;
  atspre_fprint_ldouble (stdout, f) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_ldouble (const ats_ldouble_type f) {
  atspre_stderr_view_get () ;
  atspre_fprint_ldouble (stderr, f) ;
  atspre_stderr_view_set () ;
  return ;
}

// stringization

static inline
ats_ptr_type
atspre_tostring_ldouble (const ats_ldouble_type f) {
  return atspre_tostringf ("%Lf", f) ;
}

/* ****** ****** */

#endif /* ATS_PRELUDE_FLOAT_CATS */

/* end of [float.cats] */
