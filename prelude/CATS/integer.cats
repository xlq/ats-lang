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

#ifndef ATS_PRELUDE_INTEGER_CATS
#define ATS_PRELUDE_INTEGER_CATS

/* ****** ****** */

#include <stdio.h>

/* ****** ****** */

#include "ats_exception.h"
#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

extern ats_ptr_type atspre_tostring_llint (ats_llint_type i) ;
extern ats_ptr_type atspre_tostring_ullint (ats_ullint_type u) ;

/* ****** ****** */

/* signed integers */

/* ****** ****** */

static inline
ats_int_type
atspre_int_of_char (ats_char_type c) {
  return c ;
}

static inline
ats_int_type
atspre_int_of_schar (ats_schar_type c) {
  return c ;
}

static inline
ats_int_type
atspre_int_of_uchar (ats_uchar_type c) {
  return c ;
}

//

static inline
ats_int_type
atspre_int_of_int (ats_int_type i) { return i ; }

static inline
ats_int_type
atspre_int_of_double (ats_double_type f) { return f ; }

static inline
ats_int_type
atspre_int_of_string (ats_ptr_type s)
{
  return atoi((char*)s) ;
} /* end of [atspre_int_of_string] */

static inline
ats_int_type
atspre_int_of_uint (ats_uint_type u) { return u ; }

static inline
ats_int_type
atspre_int_of_lint (ats_lint_type li) { return li ; }

//

static inline
ats_int_type
atspre_abs_int (ats_int_type i) {
  return (i >= 0 ? i : -i) ;
}

static inline
ats_int_type
atspre_neg_int (ats_int_type i) {
  return (-i) ;
}

static inline
ats_int_type
atspre_succ_int (ats_int_type i) {
  return (i + 1) ;
}

static inline
ats_int_type
atspre_pred_int (ats_int_type i) {
  return (i - 1) ;
}

static inline
ats_int_type
atspre_add_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 + i2) ;
}

static inline
ats_int_type
atspre_sub_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 - i2) ;
}

static inline
ats_int_type
atspre_mul_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 * i2) ;
}

static inline
ats_int_type
atspre_div_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 / i2) ;
}

static inline
ats_int_type
atspre_mod_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 != i2) ;
}

// compare, max and min

static inline
ats_int_type
atspre_compare_int_int (ats_int_type i1, ats_int_type i2) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
}

static inline
ats_int_type
atspre_max_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 >= i2) ? i1 : i2 ;
}

static inline
ats_int_type
atspre_min_int_int (ats_int_type i1, ats_int_type i2) {
  return (i1 <= i2) ? i1 : i2 ;
}

// square, cube and pow functions

static inline
ats_int_type
atspre_square_int (ats_int_type i) {
  return (i * i) ;
}

static inline
ats_int_type
atspre_cube_int (ats_int_type i) {
  return (i * i * i) ;
}

static inline
ats_int_type
atspre_pow_int_int1 (ats_int_type x, ats_int_type n) {
  ats_int_type res = 1;
  while (n > 0) {
    if (n % 2 > 0) { res *= x ; x = x * x ; }
    else { x = x * x ; }
    n = n >> 1 ;
  }
  return res ;
}

// greatest common division

static inline
ats_int_type
atspre_gcd_int_int (ats_int_type m0, ats_int_type n0) {
  int m, n, t ;

  if (m0 >= 0) m = m0; else m = -m0 ;
  if (n0 >= 0) n = n0; else n = -n0 ;
  while (m) { t = n % m ; n = m ; m = t ; }
  return n ;

}

// bitwise operations

static inline
ats_int_type
atspre_asl_int_int1 (ats_int_type i, ats_int_type n) {
  return i << n ;
}

static inline
ats_int_type
atspre_asr_int_int1 (ats_int_type i, ats_int_type n) {
  return i >> n ;
}

// print functions

static inline
ats_void_type
atspre_fprint_int (ats_ptr_type out, ats_int_type i) {
  int n ;
  n = fprintf ((FILE*)out, "%d", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "exit(ATS): [fprint_int] failed.\n") ;
  } /* end of [if] */
  return ;
}

static inline
ats_void_type
atspre_print_int (ats_int_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_int (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_int (ats_int_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_int (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

//

static inline
ats_void_type
atspre_fscan_int_exn (ats_ptr_type inp, ats_ref_type r) {
  int n ;
  n = fscanf ((FILE*)inp, "%d", r) ;
  if (n < 1) {
    ats_exit_errmsg (n, "exit(ATS): [fscan_int_exn] failed.\n") ;
  }
  return ;
} /* end of [atspre_fscan_int_exn] */

//

static inline
ats_ptr_type
atspre_tostring_int (ats_int_type i) {
  return atspre_tostring_llint (i) ;
}

/* ****** ****** */

/* unsigned integers */

/* ****** ****** */

static inline
ats_uint_type
atspre_uint_of_char (ats_char_type c) {
  return ((unsigned char)c) ;
}

static inline
ats_uint_type
atspre_uint_of_int (ats_int_type i) {
  return i ;
}

static inline
ats_uint_type
atspre_uint_of_double (ats_double_type d) {
  return (ats_uint_type)d ;
}

//

static inline
ats_uint_type
atspre_succ_uint (ats_uint_type i) {
  return (i + 1) ;
}

static inline
ats_uint_type
atspre_pred_uint (ats_uint_type i) {
  return (i - 1) ;
}

static inline
ats_uint_type
atspre_add_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 + i2) ;
}

static inline
ats_uint_type
atspre_sub_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 - i2) ;
}

static inline
ats_uint_type
atspre_mul_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 * i2) ;
}

static inline
ats_uint_type
atspre_div_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 / i2) ;
}

static inline
ats_uint_type
atspre_mod_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 != i2) ;
}

// compare, max and min

static inline
ats_int_type
atspre_compare_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
}

static inline
ats_uint_type
atspre_max_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 >= i2 ? i1 : i2) ;
}

static inline
ats_uint_type
atspre_min_uint_uint (ats_uint_type i1, ats_uint_type i2) {
  return (i1 <= i2 ? i1 : i2) ;
}

// bitwise operations

static inline
ats_uint_type
atspre_lnot_uint (ats_uint_type x) { return (~x) ; }

static inline
ats_uint_type
atspre_land_uint_uint (ats_uint_type x, ats_uint_type y) {
  return (x & y) ;
}

static inline
ats_uint_type
atspre_lor_uint_uint (ats_uint_type x, ats_uint_type y) {
  return (x | y) ;
}

static inline
ats_uint_type
atspre_lxor_uint_uint (ats_uint_type x, ats_uint_type y) {
  return (x ^ y) ;
}

static inline
ats_uint_type
atspre_lsl_uint_int1 (ats_uint_type i, ats_int_type n) {
  return i << n ;
}

static inline
ats_uint_type
atspre_lsr_uint_int1 (ats_uint_type i, ats_int_type n) {
  return i >> n ;
}

// print functions

static inline
ats_void_type
atspre_fprint_uint (ats_ptr_type out, ats_uint_type i) {
  int n = fprintf ((FILE*)out, "%u", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_uint] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_uint (ats_uint_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_uint(stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_uint (ats_uint_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_uint(stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

//

static inline
ats_ptr_type
atspre_tostring_uint (ats_uint_type i) {
  return atspre_tostring_ullint (i) ;
}

/* ****** ****** */

#define atspre_int1_of_int atspre_int_of_int
#define atspre_int1_of_string atspre_int_of_string

#define atspre_iabs atspre_abs_int
#define atspre_ineg atspre_neg_int

#define atspre_isucc atspre_succ_int
#define atspre_ipred atspre_pred_int

#define atspre_iadd atspre_add_int_int
#define atspre_isub atspre_sub_int_int
#define atspre_imul atspre_mul_int_int
#define atspre_imul1 atspre_mul_int_int
#define atspre_imul2 atspre_mul_int_int
#define atspre_idiv atspre_div_int_int
#define atspre_idiv1 atspre_div_int_int

#define atspre_nmul atspre_mul_int_int
#define atspre_ndiv atspre_div_int_int
#define atspre_nmod atspre_mod_int_int
#define atspre_nmod1 atspre_mod_int_int

#define atspre_ilt atspre_lt_int_int
#define atspre_ilte atspre_lte_int_int
#define atspre_igt atspre_gt_int_int
#define atspre_igte atspre_gte_int_int
#define atspre_ieq atspre_eq_int_int
#define atspre_ineq atspre_neq_int_int

#define atspre_icompare atspre_compare_int_int
#define atspre_imax atspre_max_int_int
#define atspre_imin atspre_min_int_int

#define atspre_ipow atspre_pow_int_int1
#define atspre_npow atspre_pow_int_int1

static inline
ats_int_type
atspre_ihalf (ats_int_type n) { return (n / 2) ; }

static inline
ats_int_type
atspre_nhalf (ats_int_type n) { return (n >> 1) ; }

/* ****** ****** */

static inline
ats_uint_type
atspre_uint1_of_int (ats_int_type i) { return i ; }

static inline
ats_uint_type
atspre_uint1_of_uint (ats_uint_type u) { return u ; }

//

#define atspre_uadd atspre_add_uint_uint
#define atspre_usub atspre_sub_uint_uint
#define atspre_umul atspre_mul_uint_uint
#define atspre_udiv atspre_div_uint_uint
#define atspre_umod atspre_mod_uint_uint

//

static inline
ats_int_type
atspre_uimod(ats_uint_type u1, ats_int_type i2) {
  return (u1 % ((ats_uint_type)i2)) ;
}

#define atspre_ult atspre_lt_uint_uint
#define atspre_ulte atspre_lte_uint_uint
#define atspre_ugt atspre_gt_uint_uint
#define atspre_ugte atspre_gte_uint_uint
#define atspre_ueq atspre_eq_uint_uint
#define atspre_uneq atspre_neq_uint_uint

#define atspre_ucompare atspre_compare_uint_uint
#define atspre_umax atspre_max_uint_uint
#define atspre_umin atspre_min_uint_uint

/* ****** ****** */

/* signed long integers */

/* ****** ****** */

static inline
ats_lint_type
atspre_lint_of_int (ats_int_type i) {
  return i ;
}

static inline
ats_lint_type
atspre_lint_of_string (ats_ptr_type s) {
  return atol ((char*)s) ;
}

// arithmetic functions and comparison functions

static inline
ats_lint_type
atspre_abs_lint (ats_lint_type i) {
  return (i >= 0 ? i : -i) ;
}

static inline
ats_lint_type
atspre_neg_lint (ats_lint_type i) {
  return (-i) ;
}

static inline
ats_lint_type
atspre_succ_lint (ats_lint_type i) { return (i + 1) ; }

static inline
ats_lint_type
atspre_pred_lint (ats_lint_type i) { return (i - 1) ; }

static inline
ats_lint_type
atspre_add_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 + i2) ;
}

static inline
ats_lint_type
atspre_sub_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 - i2) ;
}

static inline
ats_lint_type
atspre_mul_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 * i2) ;
}

static inline
ats_lint_type
atspre_div_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 / i2) ;
}

static inline
ats_lint_type
atspre_mod_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_lint_lint (ats_lint_type i1, ats_lint_type i2) {
  return (i1 != i2) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_lint (ats_ptr_type out, ats_lint_type i) {
  int n ;
  n = fprintf ((FILE*)out, "%li", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_lint] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_lint (ats_lint_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_lint (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_lint (ats_lint_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_lint (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

//

static inline
ats_ptr_type
atspre_tostring_lint (ats_lint_type i) {
  return atspre_tostring_llint (i) ;
}

/* ****** ****** */

/* unsigned long integers */

/* ****** ****** */

static inline
ats_ulint_type
atspre_ulint_of_int (ats_int_type i) {
  return ((ats_ulint_type)i) ;
}

static inline
ats_ulint_type
atspre_ulint_of_uint (ats_uint_type u) {
  return ((ats_ulint_type)u) ;
}

static inline
ats_ulint_type
atspre_ulint_of_lint (ats_lint_type li) {
  return ((ats_ulint_type)li) ;
}

//

static inline
ats_uint_type
atspre_uint_of_ulint (ats_ulint_type ul) {
  return ((ats_uint_type)ul) ;
}

//

static inline
ats_ulint_type
atspre_succ_ulint (ats_ulint_type i) { return (i + 1) ; }

static inline
ats_ulint_type
atspre_pred_ulint (ats_ulint_type i) { return (i - 1) ; }

static inline
ats_ulint_type
atspre_add_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 + i2) ;
}

static inline
ats_ulint_type
atspre_sub_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 - i2) ;
}

static inline
ats_ulint_type
atspre_mul_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 * i2) ;
}

static inline
ats_ulint_type
atspre_div_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 / i2) ;
}

static inline
ats_ulint_type
atspre_mod_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_ulint_ulint (ats_ulint_type i1, ats_ulint_type i2) {
  return (i1 != i2) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_ulint (ats_ptr_type out, ats_ulint_type i) {
  int n = fprintf ((FILE*)out, "%lu", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_ulint] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_ulint (ats_ulint_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_ulint (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_ulint (ats_ulint_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_ulint (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

//

static inline
ats_ptr_type
atspre_tostring_ulint (ats_ulint_type i) {
  return atspre_tostring_ullint (i) ;
}

/* ****** ****** */

/* long long integers */

/* ****** ****** */

static inline
ats_llint_type
atspre_llint_of_int (ats_int_type i) {
  return ((ats_llint_type)i) ;
}

static inline
ats_llint_type
atspre_llint_of_string (ats_ptr_type s) {
  return atoll ((char*)s) ;
}

// arithmetic functions and comparison functions

static inline
ats_llint_type
atspre_abs_llint (ats_llint_type i) {
  return (i >= 0 ? i : -i) ;
}

static inline
ats_llint_type
atspre_neg_llint (ats_llint_type i) {
  return (-i) ;
}

static inline
ats_llint_type
atspre_succ_llint (ats_llint_type i) { return (i + 1) ; }

static inline
ats_llint_type
atspre_pred_llint (ats_llint_type i) { return (i - 1) ; }

static inline
ats_llint_type
atspre_add_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 + i2) ;
}

static inline
ats_llint_type
atspre_sub_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 - i2) ;
}

static inline
ats_llint_type
atspre_mul_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 * i2) ;
}

static inline
ats_llint_type
atspre_div_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 / i2) ;
}

static inline
ats_llint_type
atspre_mod_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_llint_llint (ats_llint_type i1, ats_llint_type i2) {
  return (i1 != i2) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_llint (ats_ptr_type out, ats_llint_type i) {
  int n = fprintf ((FILE*)out, "%lli", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_llint] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_llint (ats_llint_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_llint (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_llint (ats_llint_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_llint (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

/* unsigned long long integers */

/* ****** ****** */

static inline
ats_ullint_type
atspre_ullint_of_int (ats_int_type i) {
  return ((ats_ullint_type)i) ;
}

static inline
ats_ullint_type
atspre_succ_ullint (ats_ullint_type i) { return (i + 1) ; }

static inline
ats_ullint_type
atspre_pred_ullint (ats_ullint_type i) { return (i - 1) ; }

static inline
ats_ullint_type
atspre_add_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 + i2) ;
}

static inline
ats_ullint_type
atspre_sub_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 - i2) ;
}

static inline
ats_ullint_type
atspre_mul_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 * i2) ;
}

static inline
ats_ullint_type
atspre_div_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 / i2) ;
}

static inline
ats_ullint_type
atspre_mod_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_ullint_ullint (ats_ullint_type i1, ats_ullint_type i2) {
  return (i1 != i2) ;
}

// print functions

static inline
ats_void_type
atspre_fprint_ullint (ats_ptr_type out, ats_ullint_type i) {
  int n = fprintf ((FILE*)out, "%llu", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_ullint] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_ullint (ats_ullint_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_ullint (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_ullint (ats_ullint_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_ullint (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

/* integers of fixed sizes */

/* ****** ****** */

static inline
ats_int8_type
atspre_int8_of_int (ats_int_type i) {
  return i ;
}

// ------ ------

static inline
ats_int8_type
atspre_abs_int8 (ats_int8_type i) {
  return (i >= 0 ? i : -i) ;
}

static inline
ats_int8_type
atspre_neg_int8 (ats_int8_type i) {
  return (-i) ;
}

static inline
ats_int8_type
atspre_succ_int8 (ats_int8_type i) {
  return (i + 1) ;
}

static inline
ats_int8_type
atspre_pred_int8 (ats_int8_type i) {
  return (i - 1) ;
}

static inline
ats_int8_type
atspre_add_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 + i2) ;
}

static inline
ats_int8_type
atspre_sub_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 - i2) ;
}

static inline
ats_int8_type
atspre_mul_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 * i2) ;
}

static inline
ats_int8_type
atspre_div_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 / i2) ;
}

static inline
ats_int8_type
atspre_mod_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 != i2) ;
}

// compare, max, min

static inline
ats_int_type
atspre_compare_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
}

static inline
ats_int8_type
atspre_max_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 >= i2) ? i1 : i2 ;
}

static inline
ats_int8_type
atspre_min_int8_int8 (ats_int8_type i1, ats_int8_type i2) {
  return (i1 <= i2) ? i1 : i2 ;
}

// print functions

static inline
ats_void_type
atspre_fprint_int8 (ats_ptr_type out, ats_int8_type i) {
  int n = fprintf ((FILE*)out, "%hhd", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_int8] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_int8 (ats_int8_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_int8 (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_int8 (ats_int8_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_int8 (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

static inline
ats_int16_type
atspre_int16_of_int (ats_int_type i) {
  return i ;
}

// ------ ------

static inline
ats_int16_type
atspre_abs_int16 (ats_int16_type i) {
  return (i >= 0 ? i : -i) ;
}

static inline
ats_int16_type
atspre_neg_int16 (ats_int16_type i) {
  return (-i) ;
}

static inline
ats_int16_type
atspre_succ_int16 (ats_int16_type i) {
  return (i + 1) ;
}

static inline
ats_int16_type
atspre_pred_int16 (ats_int16_type i) {
  return (i - 1) ;
}

static inline
ats_int16_type
atspre_add_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 + i2) ;
}

static inline
ats_int16_type
atspre_sub_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 - i2) ;
}

static inline
ats_int16_type
atspre_mul_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 * i2) ;
}

static inline
ats_int16_type
atspre_div_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 / i2) ;
}

static inline
ats_int16_type
atspre_mod_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 != i2) ;
}

// compare, max, min

static inline
ats_int_type
atspre_compare_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
}

static inline
ats_int16_type
atspre_max_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 >= i2) ? i1 : i2 ;
}

static inline
ats_int16_type
atspre_min_int16_int16 (ats_int16_type i1, ats_int16_type i2) {
  return (i1 <= i2) ? i1 : i2 ;
}

// print functions

static inline
ats_void_type
atspre_fprint_int16 (ats_ptr_type out, ats_int16_type i) {
  int n = fprintf ((FILE*)out, "%d", i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_int16] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_int16 (ats_int16_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_int16 (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_int16 (ats_int16_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_int16 (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

static inline
ats_int32_type
atspre_int32_of_int (ats_int_type i) {
  return i ;
}

// ------ ------

static inline
ats_int32_type
atspre_abs_int32 (ats_int32_type i) {
  return (i >= 0 ? i : -i) ;
}

static inline
ats_int32_type
atspre_neg_int32 (ats_int32_type i) {
  return (-i) ;
}

static inline
ats_int32_type
atspre_succ_int32 (ats_int32_type i) {
  return (i + 1) ;
}

static inline
ats_int32_type
atspre_pred_int32 (ats_int32_type i) {
  return (i - 1) ;
}

static inline
ats_int32_type
atspre_add_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 + i2) ;
}

static inline
ats_int32_type
atspre_sub_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 - i2) ;
}

static inline
ats_int32_type
atspre_mul_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 * i2) ;
}

static inline
ats_int32_type
atspre_div_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 / i2) ;
}

static inline
ats_int32_type
atspre_mod_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 != i2) ;
}

// compare, max, int

static inline
ats_int_type
atspre_compare_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
}

static inline
ats_int32_type
atspre_max_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 >= i2) ? i1 : i2 ;
}

static inline
ats_int32_type
atspre_min_int32_int32 (ats_int32_type i1, ats_int32_type i2) {
  return (i1 <= i2) ? i1 : i2 ;
}

// print functions

static inline
ats_void_type
atspre_fprint_int32 (ats_ptr_type out, ats_int32_type i) {
  int n ;
  n = fprintf ((FILE*)out, "%li", (ats_lint_type)i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_int32] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_int32 (ats_int32_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_int32 (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_int32 (ats_int32_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_int32 (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

static inline
ats_int64_type
atspre_int64_of_int (ats_int_type i) {
  return (i) ;
}

// ------ ------

static inline
ats_int64_type
atspre_abs_int64 (ats_int64_type i) {
  return (i >= 0 ? i : -i) ;
}

static inline
ats_int64_type
atspre_neg_int64 (ats_int64_type i) {
  return (-i) ;
}

static inline
ats_int64_type
atspre_succ_int64 (ats_int64_type i) { return (i + 1) ; }

static inline
ats_int64_type
atspre_pred_int64 (ats_int64_type i) { return (i - 1) ; }

static inline
ats_int64_type
atspre_add_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 + i2) ;
}

static inline
ats_int64_type
atspre_sub_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 - i2) ;
}

static inline
ats_int64_type
atspre_mul_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 * i2) ;
}

static inline
ats_int64_type
atspre_div_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 / i2) ;
}

static inline
ats_int64_type
atspre_mod_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 % i2) ;
}

static inline
ats_bool_type
atspre_lt_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 < i2) ;
}

static inline
ats_bool_type
atspre_lte_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 <= i2) ;
}

static inline
ats_bool_type
atspre_gt_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 > i2) ;
}

static inline
ats_bool_type
atspre_gte_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 >= i2) ;
}

static inline
ats_bool_type
atspre_eq_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 == i2) ;
}

static inline
ats_bool_type
atspre_neq_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 != i2) ;
}

// compare, max, min

static inline
ats_int_type
atspre_compare_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  if (i1 < i2) return (-1) ;
  if (i1 > i2) return ( 1) ;
  return (0) ;
}

static inline
ats_int64_type
atspre_max_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 >= i2) ? i1 : i2 ;
}

static inline
ats_int64_type
atspre_min_int64_int64 (ats_int64_type i1, ats_int64_type i2) {
  return (i1 <= i2) ? i1 : i2 ;
}

// print functions

static inline
ats_void_type
atspre_fprint_int64 (ats_ptr_type out, ats_int64_type i) {
  int n ;
  n = fprintf ((FILE*)out, "%lli", (ats_llint_type)i) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_int64] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_int64 (ats_int64_type i) {
  atspre_stdout_view_get () ;
  atspre_fprint_int64 (stdout, i) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_int64 (ats_int64_type i) {
  atspre_stderr_view_get () ;
  atspre_fprint_int64 (stderr, i) ;
  atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

#endif /* ATS_PRELUDE_INTEGER_CATS */

/* end of [integer.cats] */
