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
 * ATS is  free software;  you can redistribute it and/or modify it under
 * the  terms of the  GNU General Public License as published by the Free
 * Software Foundation; either version 2.1, or (at your option) any later
 * version.
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

/* allocation and deallocation */

static inline
ats_void_type
atslib_mpz_init(ats_mpz_ptr_type x) {
  mpz_init((mpz_ptr)x) ; return ;
}

static inline
ats_void_type
atslib_mpz_clear(ats_mpz_ptr_type x) {
  mpz_clear((mpz_ptr)x) ; return ;
}

/* ****** ****** */

// various get and set functions

// get functions

static inline
ats_int_type
atslib_mpz_get_int (ats_mpz_ptr_type x) {
  return mpz_get_si((mpz_ptr)x) ;
}

static inline
ats_lint_type
atslib_mpz_get_lint (ats_mpz_ptr_type x) {
  return mpz_get_si((mpz_ptr)x) ;
}

static inline
ats_uint_type
atslib_mpz_get_uint (ats_mpz_ptr_type x) {
  return mpz_get_ui((mpz_ptr)x) ;
}

static inline
ats_ulint_type
atslib_mpz_get_ulint (ats_mpz_ptr_type x) {
  return mpz_get_ui((mpz_ptr)x) ;
}

static inline
ats_double_type
atslib_mpz_get_double (ats_mpz_ptr_type x) {
  return mpz_get_d((mpz_ptr)x) ;
}

static inline
ats_ptr_type
atslib_mpz_get_str(ats_int_type base, ats_mpz_ptr_type x) {
  return mpz_get_str((char *)0, base, (mpz_ptr)x) ;
}

// set functions

static inline
ats_void_type
atslib_mpz_set_mpz (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  mpz_set((mpz_ptr)x, (mpz_ptr)y) ; return ;
}

static inline
ats_void_type
atslib_mpz_set_int (ats_mpz_ptr_type x, ats_int_type y) {
  mpz_set_si((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_set_lint (ats_mpz_ptr_type x, ats_lint_type y) {
  mpz_set_si((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_set_uint (ats_mpz_ptr_type x, ats_uint_type y) {
  mpz_set_ui((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_set_ulint (ats_mpz_ptr_type x, ats_ulint_type y) {
  mpz_set_ui((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_set_double (ats_mpz_ptr_type x, ats_double_type y) {
  mpz_set_d((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_set_mpq (ats_mpz_ptr_type x, ats_mpq_ptr_type y) {
  mpz_set_q((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_set_mpf (ats_mpz_ptr_type x, ats_mpf_ptr_type y) {
  mpz_set_f((mpz_ptr)x, (mpf_ptr)y) ; return ;
}

static inline
ats_int_type
atslib_mpz_set_str_err
  (ats_mpz_ptr_type x, ats_ptr_type s, ats_int_type base) {
  return mpz_set_str((mpz_ptr)x, (char*)s, base) ;
}

static inline
ats_void_type
atslib_mpz_set_str
  (ats_mpz_ptr_type x, ats_ptr_type s, ats_int_type base) {
  int n ;
  n = mpz_set_str((mpz_ptr)x, (char*)s, base) ;
  if (n < 0) {
    atspre_exit_prerrf(1, "exit(ATS): [atslib_mpz_set_str(%s)]: failed\n", s) ;
  }
  return ;
} /* end of [atslib_mpz_set_str] */

// init and set functions

static inline
ats_void_type
atslib_mpz_init_set_mpz (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  mpz_init_set((mpz_ptr)x, (mpz_ptr)y) ; return ;
}

static inline
ats_void_type
atslib_mpz_init_set_int (ats_mpz_ptr_type x, ats_int_type y) {
  mpz_init_set_si((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_init_set_lint (ats_mpz_ptr_type x, ats_lint_type y) {
  mpz_init_set_si((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_init_set_uint (ats_mpz_ptr_type x, ats_uint_type y) {
  mpz_init_set_ui((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_init_set_ulint (ats_mpz_ptr_type x, ats_ulint_type y) {
  mpz_init_set_ui((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_init_set_double (ats_mpz_ptr_type x, ats_double_type y) {
  mpz_init_set_d((mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_init_set_mpq (ats_mpz_ptr_type x, ats_mpq_ptr_type y) {
  mpz_init((mpz_ptr)x) ; mpz_set_q((mpz_ptr)x, (mpq_ptr)y); return ;
}

static inline
ats_void_type
atslib_mpz_init_set_mpf (ats_mpz_ptr_type x, ats_mpf_ptr_type y) {
  mpz_init((mpz_ptr)x) ; mpz_set_f((mpz_ptr)x, (mpf_ptr)y); return ;
}

static inline
ats_int_type atslib_mpz_init_set_str_err
  (ats_mpz_ptr_type x, ats_ptr_type s, ats_int_type base) {
  mpz_init((mpz_ptr)x) ; return atslib_mpz_set_str_err (x, s, base);
}

static inline
ats_void_type
atslib_mpz_init_set_str
  (ats_mpz_ptr_type x, ats_ptr_type s, ats_int_type base) {
  int err ;
  err = mpz_init_set_str((mpz_ptr)x, (char*)s, base) ;
  if (err < 0) {
    atspre_exit_prerrf(1, "exit(ATS): [atslib_mpz_init_set_str(%s)] failed\n", s) ;
  }
  return ;
} /* end of [atslib_mpz_init_set_str] */

/* ****** ****** */

// negation

static inline
ats_void_type
atslib_mpz_neg_2 (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  mpz_neg((mpz_ptr)x, (mpz_ptr)y) ; return ;
}

static inline
ats_void_type
atslib_mpz_neg_1 (ats_mpz_ptr_type x) {
  mpz_neg((mpz_ptr)x, (mpz_ptr)x) ; return ;
}


// absolute value

static inline
ats_void_type
atslib_mpz_abs_2 (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  mpz_abs((mpz_ptr)x, (mpz_ptr)y) ; return ;
}

static inline
ats_void_type
atslib_mpz_abs_1 (ats_mpz_ptr_type x) {
  mpz_abs((mpz_ptr)x, (mpz_ptr)x) ; return ;
}


/* addition, subtraction and multiplcation */

// addition

static inline
ats_void_type
atslib_mpz_add_mpz_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_mpz_ptr_type z) {
  mpz_add ((mpz_ptr)x, (mpz_ptr)y, (mpz_ptr)z) ; return ;
}

static inline
ats_void_type
atslib_mpz_add_int_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_int_type z) {
  if (z >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
}

static inline
ats_void_type
atslib_mpz_add_lint_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_lint_type z) {
  if (z >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
}

static inline
ats_void_type
atslib_mpz_add_uint_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_uint_type z) {
  mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_add_ulint_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_ulint_type z) {
  mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_add_mpz_2 (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  mpz_add ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)y) ; return ;
}

static inline
ats_void_type
atslib_mpz_add_int_2 (ats_mpz_ptr_type x, ats_int_type y) {
  if (y >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ;
  }
  return ;
}

static inline
ats_void_type
atslib_mpz_add_lint_2 (ats_mpz_ptr_type x, ats_lint_type y) {
  if (y >= 0) {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
  } else {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ; return ;
  }
}

static inline
ats_void_type
atslib_mpz_add_uint_2 (ats_mpz_ptr_type x, ats_uint_type y) {
  mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_add_ulint_2 (ats_mpz_ptr_type x, ats_ulint_type y) {
  mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

// subtraction

static inline
ats_void_type
atslib_mpz_sub_mpz_3 (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_mpz_ptr_type z) {
  mpz_sub ((mpz_ptr)x, (mpz_ptr)y, (mpz_ptr)z) ; return ;
}

static inline
ats_void_type
atslib_mpz_sub_int_3 (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_int_type z) {
  if (z >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
}

static inline
ats_void_type
atslib_mpz_sub_lint_3 (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_lint_type z) {
  if (z >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, z) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)y, -z) ;
  }
  return ;
}

static inline
ats_void_type
atslib_mpz_sub_uint_3 (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_uint_type z) {
  mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_sub_ulint_3 (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_ulint_type z) {
  mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_sub_mpz_2 (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  mpz_sub ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)y) ; return ;
}

static inline
ats_void_type
atslib_mpz_sub_int_2 (ats_mpz_ptr_type x, ats_int_type y) {
  if (y >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ;
  }
  return ;
}

static inline
ats_void_type
atslib_mpz_sub_lint_2 (ats_mpz_ptr_type x, ats_lint_type y) {
  if (y >= 0) {
    mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ;
  } else {
    mpz_add_ui ((mpz_ptr)x, (mpz_ptr)x, -y) ;
  }
  return ;
}

static inline
ats_void_type
atslib_mpz_sub_uint_2 (ats_mpz_ptr_type x, ats_uint_type y) {
  mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_sub_ulint_2 (ats_mpz_ptr_type x, ats_ulint_type y) {
  mpz_sub_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

// multiplication

static inline
ats_void_type
atslib_mpz_mul_mpz_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_mpz_ptr_type z) {
  mpz_mul ((mpz_ptr)x, (mpz_ptr)y, (mpz_ptr)z) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_int_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_int_type z) {
  mpz_mul_si ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_lint_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_lint_type z) {
  mpz_mul_si ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_uint_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_uint_type z) {
  mpz_mul_ui ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_ulint_3
  (ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_ulint_type z) {
  mpz_mul_ui ((mpz_ptr)x, (mpz_ptr)y, z) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_mpz_2 (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  mpz_mul ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)y) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_int_2 (ats_mpz_ptr_type x, ats_int_type y) {
  mpz_mul_si ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_lint_2 (ats_mpz_ptr_type x, ats_lint_type y) {
  mpz_mul_si ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_uint_2 (ats_mpz_ptr_type x, ats_uint_type y) {
  mpz_mul_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_ulint_2 (ats_mpz_ptr_type x, ats_ulint_type y) {
  mpz_mul_ui ((mpz_ptr)x, (mpz_ptr)x, y) ; return ;
}

static inline
ats_void_type
atslib_mpz_mul_mpz_1 (ats_mpz_ptr_type x) {
  mpz_mul ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)x) ; return ;
}

// division

static inline
ats_void_type
atslib_mpz_tdiv_q_mpz_3
  (ats_mpz_ptr_type q, ats_mpz_ptr_type n, ats_mpz_ptr_type d) {
  mpz_tdiv_q ((mpz_ptr)q, (mpz_ptr)n, (mpz_ptr)d) ; return ;
}

static inline
ats_void_type
atslib_mpz_tdiv_q_ulint_3
  (ats_mpz_ptr_type q, ats_mpz_ptr_type n, ats_ulint_type d) {
  mpz_tdiv_q_ui ((mpz_ptr)q, (mpz_ptr)n, d) ; return ;
}

static inline
ats_void_type
atslib_mpz_tdiv_q_mpz_2 (ats_mpz_ptr_type x, ats_mpz_ptr_type d) {
  mpz_tdiv_q ((mpz_ptr)x, (mpz_ptr)x, (mpz_ptr)d) ; return ;
}

static inline
ats_void_type
atslib_mpz_tdiv_q_ulint_2 (ats_mpz_ptr_type x, ats_ulint_type d) {
  mpz_tdiv_q_ui ((mpz_ptr)x, (mpz_ptr)x, d) ; return ;
}

// add/mul and submul compibination

static inline
ats_void_type
atslib_mpz_addmul_mpz_3 (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_mpz_ptr_type z
) {
  mpz_addmul_mpz ((mpz_ptr)x, (mpz_ptr)y, (mpz_ptr)z) ; return ;
} /* end of [atslib_mpz_addmul_mpz_3] */

static inline
ats_void_type
atslib_mpz_addmul_uint_3 (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_uint_type z
) {
  mpz_addmul_ui ((mpz_ptr)x, (mpz_ptr)y, (unsigned int)z) ; return ;
} /* end of [atslib_mpz_addmul_mpz_3] */

static inline
ats_void_type
atslib_mpz_submul_mpz_3 (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_mpz_ptr_type z
) {
  mpz_submul_mpz ((mpz_ptr)x, (mpz_ptr)y, (mpz_ptr)z) ; return ;
} /* end of [atslib_mpz_submul_uint_3] */

static inline
ats_void_type
atslib_mpz_submul_uint_3 (
  ats_mpz_ptr_type x, ats_mpz_ptr_type y, ats_uint_type z
) {
  mpz_submul_ui ((mpz_ptr)x, (mpz_ptr)y, (unsigned int)z) ; return ;
} /* end of [atslib_mpz_submul_uint_3] */

/* ****** ****** */

// comparison

static inline
ats_int_type
atslib_mpz_cmp_mpz (ats_mpz_ptr_type x, ats_mpz_ptr_type y) {
  return mpz_cmp((mpz_ptr)x, (mpz_ptr)y) ;
}

static inline
ats_int_type
atslib_mpz_cmp_int (ats_mpz_ptr_type x, ats_int_type y) {
  return mpz_cmp_si((mpz_ptr)x, y) ;
}

static inline
ats_int_type
atslib_mpz_cmp_lint (ats_mpz_ptr_type x, ats_lint_type y) {
  return mpz_cmp_si((mpz_ptr)x, y) ;
}

static inline
ats_int_type
atslib_mpz_cmp_uint (ats_mpz_ptr_type x, ats_uint_type y) {
  return mpz_cmp_ui((mpz_ptr)x, y) ;
}

static inline
ats_int_type
atslib_mpz_cmp_ulint (ats_mpz_ptr_type x, ats_ulint_type y) {
  return mpz_cmp_ui((mpz_ptr)x, y) ;
}

/* ****** ****** */

// print functions

static inline
ats_int_type
atslib_mpz_out_str_err
  (ats_ptr_type file, ats_int_type base, const ats_mpz_ptr_type x) {
  return mpz_out_str((FILE*)file, base, (mpz_ptr)x) ;
}

static inline
ats_void_type
atslib_mpz_out_str
  (ats_ptr_type file, ats_int_type base, const ats_mpz_ptr_type x) {
  int n = mpz_out_str((FILE*)file, base, (mpz_ptr)x) ;
  if (!n) {
    ats_exit_errmsg (1, "exit(ATS): [atslib_mpz_out_str] failed.\n") ;
  }
  return ;
} /* end of [atslib_mpz_out_str] */

static inline
ats_void_type
atslib_fprint_mpz(ats_ptr_type file, const ats_mpz_ptr_type x) {
  mpz_out_str((FILE*)file, 10, (mpz_ptr)x) ; return ;
}

static inline
ats_void_type
atslib_print_mpz(const ats_mpz_ptr_type x) {
  atspre_stdout_view_get() ;
  atslib_fprint_mpz(stdout, x) ;
  atspre_stdout_view_set() ;
  return ;
}

static inline
ats_void_type
atslib_prerr_mpz(const ats_mpz_ptr_type x) {
  atspre_stderr_view_get() ;
  atslib_fprint_mpz(stderr, x) ;
  atspre_stderr_view_set() ;
  return ;
}

/* ****** ****** */

// stringization

static inline
ats_ptr_type
atslib_tostring_mpz (const ats_mpz_ptr_type x) {
  return mpz_get_str((char *)0, 10, (mpz_ptr)x) ;
}

/* ****** ****** */

#endif /* ATS_LIBC_GMP_CATS */
