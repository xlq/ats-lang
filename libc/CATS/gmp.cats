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

#ifndef ATS_LIBC_GMP_CATS
#define ATS_LIBC_GMP_CATS

/* ****** ****** */

#include <stdio.h>
#include <gmp.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

#include "prelude/CATS/basics.cats"

/* ****** ****** */

typedef unsigned long int ulint ;

/* ****** ****** */

// mpz_t is one element array of __mpz_struct
typedef __mpz_struct ats_mpz_viewt0ype ;

// mpq_t is one element array of __mpq_struct
typedef __mpq_struct ats_mpq_viewt0ype ;

// mpf_t is one element array of __mpf_struct
typedef __mpf_struct ats_mpf_viewt0ype ;

// [mpz_ptr] is defined in [gmp.h]

// call-by-reference
typedef ats_ref_type ats_mpz_ptr_type ;
typedef ats_ref_type ats_mpq_ptr_type ;
typedef ats_ref_type ats_mpf_ptr_type ;

/* ****** ****** */

//
// init/clear/realloc
//

#define atslib_mpz_init mpz_init
#define atslib_mpz_init2 mpz_init2
#define atslib_mpz_clear mpz_clear
#define atslib_mpz_realloc2 mpz_realloc2

/* ****** ****** */
//
// HX: integral number operations
//
/* ****** ****** */

//
// get functions
//

#define atslib_mpz_get_int mpz_get_si
#define atslib_mpz_get_uint mpz_get_ui
#define atslib_mpz_get_lint mpz_get_si
#define atslib_mpz_get_ulint mpz_get_ui
#define atslib_mpz_get_double mpz_get_d

ATSinline()
ats_ptr_type
atslib_mpz_get_str (
  ats_int_type base, ats_mpz_ptr_type x
) {
  return mpz_get_str((char*)0, base, (mpz_ptr)x) ;
} // end of [atslib_mpz_get_str]

//
// set functions
//

#define atslib_mpz_set_mpz mpz_set
#define atslib_mpz_set_int mpz_set_si
#define atslib_mpz_set_uint mpz_set_ui
#define atslib_mpz_set_lint mpz_set_si
#define atslib_mpz_set_ulint mpz_set_ui
#define atslib_mpz_set_double mpz_set_d
#define atslib_mpz_set_mpq mpz_set_q
#define atslib_mpz_set_mpf mpz_set_f
#define atslib_mpz_set_str_err mpz_set_str

ATSinline()
ats_void_type
atslib_mpz_set_str_exn (
  ats_mpz_ptr_type x, ats_ptr_type s, ats_int_type base
) {
  int n ;
  n = mpz_set_str((mpz_ptr)x, (char*)s, base) ;
  if (n < 0) {
    atspre_exit_prerrf(1, "exit(ATS): [atslib_mpz_set_str(%s)]: failed\n", s) ;
  } // end of [if]
  return ;
} // end of [atslib_mpz_set_str_exn]

//
// init and set functions
//

#define atslib_mpz_init_set_mpz mpz_init_set
#define atslib_mpz_init_set_int mpz_init_set_si
#define atslib_mpz_init_set_uint mpz_init_set_ui
#define atslib_mpz_init_set_lint mpz_init_set_si
#define atslib_mpz_init_set_ulint mpz_init_set_ui
#define atslib_mpz_init_set_double mpz_init_set_d

ATSinline()
ats_void_type
atslib_mpz_init_set_mpq (ats_mpz_ptr_type x, ats_mpq_ptr_type y) {
  mpz_init((mpz_ptr)x) ; mpz_set_q((mpz_ptr)x, (mpq_ptr)y); return ;
}

ATSinline()
ats_void_type
atslib_mpz_init_set_mpf (ats_mpz_ptr_type x, ats_mpf_ptr_type y) {
  mpz_init((mpz_ptr)x) ; mpz_set_f((mpz_ptr)x, (mpf_ptr)y); return ;
}

ATSinline()
ats_int_type
atslib_mpz_init_set_str_err
  (ats_mpz_ptr_type x, ats_ptr_type s, ats_int_type base) {
  mpz_init((mpz_ptr)x) ; return atslib_mpz_set_str_err (x, s, base);
} // end of [atslib_mpz_init_set_str_err]

ATSinline()
ats_void_type
atslib_mpz_init_set_str_exn
  (ats_mpz_ptr_type x, ats_ptr_type s, ats_int_type base) {
  int err ;
  err = mpz_init_set_str((mpz_ptr)x, (char*)s, base) ;
  if (err < 0) {
    atspre_exit_prerrf(1, "exit(ATS): [atslib_mpz_init_set_str(%s)] failed\n", s) ;
  }
  return ;
} /* end of [atslib_mpz_init_set_str_exn] */

/* ****** ****** */

//
// negation
//

#define atslib_mpz_neg2 mpz_neg

ATSinline()
ats_void_type
atslib_mpz_neg1
  (ats_mpz_ptr_type x) {
  mpz_neg((mpz_ptr)x, (mpz_ptr)x) ; return ;
} // end of [atslib_mpz_neg1]

//
// absolute value
//

#define atslib_mpz_abs2 mpz_abs

ATSinline()
ats_void_type
atslib_mpz_abs1
  (ats_mpz_ptr_type x) {
  mpz_abs((mpz_ptr)x, (mpz_ptr)x) ; return ;
} // end of [atslib_mpz_abs1]

/* ****** ****** */

//
// addition, subtraction and multiplcation
//

/* ****** ****** */

//
// addition
//

#define atslib_mpz_add3_mpz mpz_add

ATSinline()
ats_void_type
atslib_mpz_add3_int (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_int_type z
) {
  if (z >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
} // end of [atslib_mpz_add3_int]

#define atslib_mpz_add3_uint mpz_add_ui

ATSinline()
ats_void_type
atslib_mpz3_add_lint
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_lint_type z) {
  if (z >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
} // end of [atslib_mpz_add3_lint]

#define atslib_mpz_add3_ulint mpz_add_ui

//

ATSinline()
ats_void_type
atslib_mpz_add2_mpz (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y
) {
  mpz_add ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)y) ; return ;
} // end of [atslib_mpz_add2_mpz]

ATSinline()
ats_void_type
atslib_mpz_add2_int (
  ats_mpz_ptr_type x, ats_int_type y
) {
  if (y >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ;
  }
  return ;
} // end of [atslib_mpz_add2_int]

ATSinline()
ats_void_type
atslib_mpz_add2_uint (
  ats_mpz_ptr_type x, ats_uint_type y
) {
  mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

ATSinline()
ats_void_type
atslib_mpz_add2_lint (
  ats_mpz_ptr_type x, ats_lint_type y
) {
  if (y >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ;
  }
  return ;
} // end of [atslib_mpz_add2_lint]

ATSinline()
ats_void_type
atslib_mpz_add2_ulint (
  ats_mpz_ptr_type x, ats_ulint_type y
) {
  mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
} // end of [atslib_mpz_add2_ulint]

//
// subtraction
//

#define atslib_mpz_sub3_mpz mpz_sub

ATSinline()
ats_void_type
atslib_mpz_sub3_int (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_int_type z
) {
  if (z >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
} // end of [atslib_mpz_sub3_int]

#define atslib_mpz_sub3_uint mpz_sub_ui

ATSinline()
ats_void_type
atslib_mpz_sub3_lint (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_lint_type z
) {
  if (z >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
} // end of [atslib_mpz_sub3_lint]

#define atslib_mpz_sub3_ulint mpz_sub_ui

ATSinline()
ats_void_type
atslib_mpz_sub2_mpz (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y
) {
  mpz_sub ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)y) ; return ;
} // end of [atslib_mpz_sub2_mpz]

ATSinline()
ats_void_type
atslib_mpz_sub2_int (
  ats_mpz_ptr_type x, ats_int_type y
) {
  if (y >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ;
  }
  return ;
} // end of [atslib_mpz_sub2_int]

ATSinline()
ats_void_type
atslib_mpz_sub2_uint (
  ats_mpz_ptr_type x, ats_uint_type y
) {
  mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
} // end of [atslib_mpz_sub2_uint]

ATSinline()
ats_void_type
atslib_mpz_sub2_lint (
  ats_mpz_ptr_type x, ats_lint_type y
) {
  if (y >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ;
  }
  return ;
} // end of [atslib_mpz_sub2_lint]

ATSinline()
ats_void_type
atslib_mpz_sub2_ulint (
  ats_mpz_ptr_type x, ats_ulint_type y
) {
  mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
} // end of [atslib_mpz_sub2_ulint]

//
// multiplication
//

#define atslib_mpz_mul3_mpz mpz_mul
#define atslib_mpz_mul3_int mpz_mul_si
#define atslib_mpz_mul3_uint mpz_mul_ui
#define atslib_mpz_mul3_lint mpz_mul_si
#define atslib_mpz_mul3_ulint mpz_mul_ui

ATSinline()
ats_void_type
atslib_mpz_mul2_mpz (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y
) {
  mpz_mul ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)y) ; return ;
} // end of [atslib_mpz_mul2_mpz]

ATSinline()
ats_void_type
atslib_mpz_mul2_int (
  ats_mpz_ptr_type x, ats_int_type y
) {
  mpz_mul_si ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
} // end of [atslib_mpz_mul2_int]

ATSinline()
ats_void_type
atslib_mpz_mul2_uint (
  ats_mpz_ptr_type x, ats_uint_type y
) {
  mpz_mul_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
} // end of [atslib_mpz_mul2_uint]

ATSinline()
ats_void_type
atslib_mpz_mul2_lint (
  ats_mpz_ptr_type x, ats_lint_type y
) {
  mpz_mul_si ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
} // end of [atslib_mpz_mul2_lint]

ATSinline()
ats_void_type
atslib_mpz_mul2_ulint (
  ats_mpz_ptr_type x, ats_ulint_type y
) {
  mpz_mul_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
} // end of [atslib_mpz_mul2_ulint]

ATSinline()
ats_void_type
atslib_mpz_mul1_mpz
  (ats_mpz_ptr_type x) {
  mpz_mul ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)x) ; return ;
} // end of [atslib_mpz_mul1_mpz]

ATSinline()
ats_void_type
atslib_mpz_mul_2exp ( // x = y * 2^n
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_int_type n
) {
  mpz_mul_2exp((mpz_ptr)x, (mpz_ptr)y, n) ; return ;
} // end of [atslib_mpz_mul_2exp]

/* ****** ****** */

//
// truncate division
//

#define atslib_mpz_tdiv4_qr_mpz mpz_tdiv_qr
#define atslib_mpz_tdiv4_qr_ulint mpz_tdiv_qr_ui

#define atslib_mpz_tdiv3_q_mpz mpz_tdiv_q
#define atslib_mpz_tdiv3_q_ulint mpz_tdiv_q_ui

ATSinline()
ats_void_type
atslib_mpz_tdiv2_q_mpz (
  ats_mpz_ptr_type x, ats_mpz_ptr_type d
) {
  mpz_tdiv_q ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)d) ; return ;
} // end of [atslib_mpz_tdiv2_q_mpz]

ATSinline()
ats_void_type
atslib_mpz_tdiv2_q_ulint (
  ats_mpz_ptr_type x, ats_ulint_type d
) {
  mpz_tdiv_q_ui ((mpz_ptr)x, (mpz_ptr)x, d) ; return ;
} // end of [atslib_mpz_tdiv2_q_ulint]

/* ****** ****** */

//
// floor division
//

#define atslib_mpz_fdiv4_qr_mpz mpz_fdiv_qr
#define atslib_mpz_fdiv4_qr_ulint mpz_fdiv_qr_ui

#define atslib_mpz_fdiv3_q_mpz mpz_fdiv_q
#define atslib_mpz_fdiv3_q_ulint mpz_fdiv_q_ui

ATSinline()
ats_void_type
atslib_mpz_fdiv2_q_mpz (
  ats_mpz_ptr_type x, ats_mpz_ptr_type d
) {
  mpz_fdiv_q ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)d) ; return ;
} // end of [atslib_mpz_fdiv2_q_mpz]

ATSinline()
ats_void_type
atslib_mpz_fdiv2_q_ulint (
  ats_mpz_ptr_type x, ats_ulint_type d
) {
  mpz_fdiv_q_ui ((mpz_ptr)x, (mpz_ptr)x, d) ; return ;
} // end of [atslib_mpz_fdiv2_q_ulint]

/* ****** ****** */

#define atslib_mpz_mod3_mpz mpz_mod
#define atslib_mpz_mod3_ulint mpz_mod_ui

/* ****** ****** */

// addmul and submul compibination

#define atslib_mpz_addmul3_mpz  mpz_addmul
#define atslib_mpz_addmul3_uint mpz_addmul_ui
#define atslib_mpz_submul3_mpz mpz_submul
#define atslib_mpz_submul3_uint mpz_submul_ui

/* ****** ****** */

// comparison

#define atslib_mpz_cmp_mpz mpz_cmp
#define atslib_mpz_cmp_int mpz_cmp_si
#define atslib_mpz_cmp_uint mpz_cmp_ui
#define atslib_mpz_cmp_lint mpz_cmp_si
#define atslib_mpz_cmp_ulint mpz_cmp_ui

ATSinline()
ats_int_type
atslib_mpz_sgn (ats_mpz_ptr_type x) { return mpz_cmp_si((mpz_ptr)x, 0) ; }

/* ****** ****** */

// print functions

#define atslib_mpz_out_str_err mpz_out_str

ATSinline()
ats_void_type
atslib_mpz_out_str_exn (
  ats_ptr_type file
, ats_int_type base
, const ats_mpz_ptr_type x
) {
  int n = mpz_out_str((FILE*)file, base, (mpz_ptr)x) ;
  if (!n) {
    ats_exit_errmsg (1, "exit(ATS): [mpz_out_str] failed.\n") ;
  } // end of [if]
  return ;
} // end of [atslib_mpz_out_str_exn]

ATSinline()
ats_void_type
atslib_fprint_mpz (
  ats_ptr_type file, const ats_mpz_ptr_type x
) {
  atslib_mpz_out_str_exn (file, 10, x) ; return ;
} // end of [atslib_fprint_mpz]

ATSinline()
ats_void_type
atslib_print_mpz (
  const ats_mpz_ptr_type x
) {
  atspre_stdout_view_get() ;
  atslib_fprint_mpz(stdout, x) ;
  atspre_stdout_view_set() ;
  return ;
} // end of [atslib_print_mpz]

ATSinline()
ats_void_type
atslib_prerr_mpz (
  const ats_mpz_ptr_type x
) {
  atspre_stderr_view_get() ;
  atslib_fprint_mpz(stderr, x) ;
  atspre_stderr_view_set() ;
  return ;
} // end of [atslib_prerr_mpz]

/* ****** ****** */

// stringization

ATSinline()
ats_ptr_type
atslib_tostring_mpz (
  const ats_mpz_ptr_type x
) {
  return mpz_get_str((char*)0, 10, (mpz_ptr)x) ;
} // end of [atslib_tostring_mpz]

/* ****** ****** */
//
// HX: floating number operations
//
/* ****** ****** */

#define atslib_mpf_get_default_prec mpf_get_default_prec
#define atslib_mpf_set_default_prec mpf_set_default_prec

/* ****** ****** */

#define atslib_mpf_init mpf_init
#define atslib_mpf_init2 mpf_init2
#define atslib_mpf_clear mpf_clear

#define atslib_mpf_get_prec mpf_get_prec
#define atslib_mpf_set_prec mpf_set_prec
#define atslib_mpf_set_prec_raw mpf_set_prec_raw

#define atslib_mpf_get_d mpf_get_d
#define atslib_mpf_get_d_2exp mpf_get_d_2exp
#define atslib_mpf_get_si mpf_get_si
#define atslib_mpf_get_ui mpf_get_ui

#define atslib_mpf_set_mpf mpf_set
#define atslib_mpf_set_si mpf_set_si
#define atslib_mpf_set_ui mpf_set_ui
#define atslib_mpf_set_d mpf_set_d
#define atslib_mpf_set_z mpf_set_z
#define atslib_mpf_set_q mpf_set_q
#define atslib_mpf_set_str mpf_set_str

#define atslib_mpf_init_set_mpf mpf_init_set
#define atslib_mpf_init_set_si mpf_init_set_si
#define atslib_mpf_init_set_ui mpf_init_set_ui
#define atslib_mpf_init_set_d mpf_init_set_d

#define atslib_mpf_swap mpf_swap

/* ****** ****** */

#define atslib_mpf_ceil mpf_ceil
#define atslib_mpf_floor mpf_floor
#define atslib_mpf_trunc mpf_trunc
#define atslib_mpf_integer_p mpf_integer_p

/* ****** ****** */

#define abslib_mpf_neg2 mpf_neg2

ATSinline()
ats_void_type
atslib_mpf_neg1 (ats_ref_type x) {
  mpf_neg ((mpf_ptr)x, (mpf_ptr)x) ; return ;
} // end of [atslib_mpf_neg1]

#define abslib_mpf_abs2 mpf_abs2

ATSinline()
ats_void_type
atslib_mpf_abs1 (ats_ref_type x) {
  mpf_abs ((mpf_ptr) x, (mpf_ptr) x) ; return ;
} // end of [atslib_mpf_abs1]

/* ****** ****** */

#define atslib_mpf_add3_mpf mpf_add
#define atslib_mpf_add3_mpf_ui mpf_add_ui

ATSinline()
ats_void_type
atslib_mpf_add2_mpf (
  ats_ref_type rop, ats_ref_type lop2
) {
  mpf_add ((mpf_ptr)rop, (mpf_ptr) rop, (mpf_ptr)lop2); return ;
} // end of [atslib_mpf_add2_mpf]

ATSinline()
ats_void_type
atslib_mpf_add2_ui (
  ats_ref_type rop, ats_ulint_type lop2
) {
  mpf_add_ui ((mpf_ptr)rop, (mpf_ptr)rop, (ulint)lop2) ; return ;
} // end of [atslib_mpf_add2_ui]

/* ****** ****** */

#define atslib_mpf_sub3_mpf mpf_sub
#define atslib_mpf_sub3_ui mpf_sub_ui
#define atslib_mpf_ui_sub3 mpf_ui_sub

ATSinline()
ats_void_type
atslib_mpf_sub2_mpf (
  ats_ref_type rop, ats_ref_type lop2
) {
  mpf_sub ((mpf_ptr) rop, (mpf_ptr) rop, (mpf_ptr) lop2) ; return ;
} // end of [atslib_mpf_sub2_mpf]


ATSinline()
ats_void_type
atslib_mpf_sub2_ui (
  ats_ref_type rop, ats_ulint_type lop2
) {
  mpf_sub_ui ((mpf_ptr)rop, (mpf_ptr)rop, (ulint)lop2) ; return ;
} // end of [atslib_mpf_sub2_ui]

/* ****** ****** */

#define atslib_mpf_mul3_mpf mpf_mul
#define atslib_mpf_mul3_ui mpf_mul_ui

ATSinline()
ats_void_type
my_mpf_mul2 (
  ats_ref_type rop, ats_ref_type lop1
) {
  mpf_mul ((mpf_ptr)rop, (mpf_ptr)rop, (mpf_ptr)lop1) ; return ;
} // end of [my_mpf_mul2]

ATSinline()
ats_void_type
my_mpf_mul2_ui (
  ats_ref_type rop, ats_ulint_type lop2
) {
  mpf_mul_ui ((mpf_ptr)rop, (mpf_ptr)rop, (ulint)lop2) ; return ;
} // end of [my_mpf_mul2_ui]

/* ****** ****** */

#define atslib_mpf_div3_mpf mpf_div
#define atslib_mpf_div3_ui mpf_div_ui
#define atslib_mpf_ui_div3 mpf_ui_div

ATSinline()
ats_void_type
atslib_mpf_div2_mpf
(ats_ref_type rop, ats_ref_type lop1) {
  mpf_div ((mpf_ptr)rop, (mpf_ptr)rop, (mpf_ptr)lop1) ; return ;
} // end of [atslib_mpf_div2_mpf]

ATSinline()
ats_void_type
atslib_mpf_div2_ui (
  ats_ref_type rop, ats_ulint_type lop2
) {
  mpf_div_ui ((mpf_ptr)rop, (mpf_ptr)rop, (ulint)lop2) ; return ;
} // end of [atslib_mpf_div2_ui]

/* ****** ****** */

#define atslib_mpf_sqrt_mpf mpf_sqrt
#define atslib_mpf_sqrt_ui mpf_sqrt_ui

/* ****** ****** */

#endif /* ATS_LIBC_GMP_CATS */
