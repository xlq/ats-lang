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
 * Copyright (C) 2002-2009 Hongwei Xi.
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

#ifndef ATS_PRELUDE_SIZETYPE_CATS
#define ATS_PRELUDE_SIZETYPE_CATS

/* ****** ****** */

#include <stdio.h>
#include <limits.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

#define atspre_int_of_size atspre_int1_of_size1
#define atspre_size_of_int1 atspre_size1_of_int1
#define atspre_add_size_size atspre_add_size1_size1
#define atspre_mul_size_size atspre_mul_size1_size1

/* ****** ****** */

static inline
ats_int_type
atspre_int1_of_size1 (ats_size_type sz) {
  if (INT_MAX < sz) {
    fprintf (stderr, "[ats_int_of_size(%lu)] failed\n", sz) ; exit (1) ;
  } /* end of [if] */
  return ((ats_int_type)sz) ;
} /* end of [atspre_int1_of_size1] */

/* ****** ****** */

static inline
ats_size_type
atspre_size1_of_size (ats_size_type sz) { return sz ; }

static inline
ats_size_type
atspre_size1_of_int1 (ats_int_type i) { return (ats_size_type)i ; }

static inline
ats_size_type
atspre_size1_of_ssize1 (ats_ssize_type ssz) { return (ats_size_type)ssz ; }

static inline
ats_size_type
atspre_size1_of_ptrdiff1 (ats_ptrdiff_type x) { return (ats_size_type)x ; }

/* ****** ****** */

// print functions

static inline
ats_void_type
atspre_fprint_size (ats_ptr_type out, ats_size_type sz) {
  int n ;
  n = fprintf ((FILE*)out, "%lu", sz) ;
  if (n < 0) {
    ats_exit_errmsg (n, "exit(ATS): [fprint_size] failed.\n") ;
  } /* end of [if] */
  return ;
} /* end of [atspre_fprint_size] */

static inline
ats_void_type
atspre_print_size (ats_size_type sz) {
  atspre_stdout_view_get () ; atspre_fprint_size (stdout, sz) ; atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_size (ats_size_type sz) {
  atspre_stderr_view_get () ; atspre_fprint_size (stderr, sz) ; atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

static inline
ats_size_type
atspre_succ_size1 (ats_size_type sz) { return (sz + 1) ; }

static inline
ats_size_type
atspre_pred_size1 (ats_size_type sz) { return (sz - 1) ; }

/* ****** ****** */

static inline
ats_size_type
atspre_add_size1_size1 (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 + sz2) ;
}

static inline
ats_size_type
atspre_add_size1_int1 (ats_size_type sz1, ats_int_type i2) {
  return (sz1 + i2) ;
}

// ------ ------

static inline
ats_size_type
atspre_sub_size1_size1 (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 - sz2) ;
}

static inline
ats_size_type
atspre_sub_size1_int1 (ats_size_type sz1, ats_int_type i2) {
  return (sz1 - i2) ;
}

/* ****** ****** */

static inline
ats_size_type
atspre_mul_size1_size1 (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 * sz2) ;
}

#define atspre_mul1_size1_size1 atspre_mul_size1_size1
#define atspre_mul2_size1_size1 atspre_mul_size1_size1

static inline
ats_size_type
atspre_div_size1_size1 (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 / sz2) ;
} /* end of [atspre_div_size1_size1] */

static inline
ats_size_type
atspre_mod_size1_size1 (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 % sz2) ;
} /* end of [atspre_mod_size1_size1] */

#define atspre_mod1_size1_size1 atspre_mod_size1_size1

/* ****** ****** */

static inline
ats_bool_type
atspre_lt_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 < sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lt_size1_size1] */

static inline
ats_bool_type
atspre_lt_int1_size1
  (ats_int_type i1, ats_size_type sz2) {
  return (i1 < sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lt_int1_size1] */

static inline
ats_bool_type
atspre_lt_size1_int1
  (ats_int_type sz1, ats_size_type i2) {
  return (sz1 < i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lt_size1_int1] */

/* ****** ****** */

static inline
ats_bool_type
atspre_lte_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 <= sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lte_size1_size1] */

static inline
ats_bool_type
atspre_lte_int1_size1
  (ats_int_type i1, ats_size_type sz2) {
  return (i1 <= sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lte_int1_size1] */

static inline
ats_bool_type
atspre_lte_size1_int1
  (ats_int_type sz1, ats_size_type i2) {
  return (sz1 <= i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lte_size1_int1] */

/* ****** ****** */

static inline
ats_bool_type
atspre_gt_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 > sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_gt_size1_size1] */

static inline
ats_bool_type
atspre_gt_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 > i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_gt_size1_int1] */

// ------ ------

static inline
ats_bool_type
atspre_gte_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 >= sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_gte_size1_size1] */

static inline
ats_bool_type
atspre_gte_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 >= i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_gte_size1_int1] */

/* ****** ****** */

static inline
ats_bool_type
atspre_eq_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 == sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_eq_size1_size1] */

static inline
ats_bool_type
atspre_eq_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 == i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_eq_size1_int1] */

/* ****** ****** */

static inline
ats_bool_type
atspre_neq_size1_size1
  (ats_size_type sz1, ats_size_type sz2) {
  return (sz1 != sz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_neq_size1_size1] */

static inline
ats_bool_type
atspre_neq_size1_int1
  (ats_size_type sz1, ats_int_type i2) {
  return (sz1 != i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_neq_size1_int1] */

/* ****** ****** */

// signed size type

/* ****** ****** */

static inline
ats_int_type
atspre_int_of_ssize (ats_ssize_type ssz) {
  if (INT_MAX < ssz || ssz < INT_MIN) {
    fprintf (stderr, "[ats_int_of_ssize(%li)] failed\n", ssz) ; exit (1) ;
  } /* end of [if] */
  return (ats_int_type)ssz ;
} /* end of [atspre_int_of_ssize] */

static inline
ats_ssize_type atspre_ssize_of_int (ats_int_type i) {
  return (ats_ssize_type)i ;
}

static inline
ats_ssize_type atspre_ssize_of_size (ats_size_type sz) {
  ats_ssize_type ssz = sz ;
  if (ssz < 0) {
    fprintf (stderr, "[ats_ssize_of_size(%lu)] failed\n", sz) ; exit (1) ;
  } /* end of [if] */
  return ssz ;
} /* end of [atspre_ssize_of_size] */

/* ****** ****** */

// print functions

static inline
ats_void_type
atspre_fprint_ssize (ats_ptr_type out, ats_ssize_type ssz) {
  int n ;
  n = fprintf ((FILE*)out, "%li", ssz) ;
  if (n < 0) {
    ats_exit_errmsg (n, "exit(ATS): [fprint_ssize] failed.\n") ;
  } /* end of [if] */
  return ;
} /* end of [atspre_fprint_ssize] */

static inline
ats_void_type
atspre_print_ssize (ats_ssize_type ssz) {
  atspre_stdout_view_get () ; atspre_fprint_ssize (stdout, ssz) ; atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_ssize (ats_size_type ssz) {
  atspre_stderr_view_get () ; atspre_fprint_ssize (stderr, ssz) ; atspre_stderr_view_set () ;
  return ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_lt_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 < i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lt_ssize1_int1] */

// ------ ------

static inline
ats_bool_type
atspre_lte_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 <= i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_lte_ssize1_int1] */

/* ****** ****** */

static inline
ats_bool_type
atspre_gt_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 > i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_gt_ssize1_int1] */

// ------ ------

static inline
ats_bool_type
atspre_gte_ssize1_int1
  (ats_ssize_type ssz1, ats_int_type i2) {
  return (ssz1 >= i2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_gte_ssize1_int1] */

/* ****** ****** */

static inline
ats_bool_type
atspre_eq_ssize1_ssize1
  (ats_ssize_type ssz1, ats_ssize_type ssz2) {
  return (ssz1 == ssz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_eq_ssize1_ssize1] */

static inline
ats_bool_type
atspre_neq_ssize1_ssize1
  (ats_ssize_type ssz1, ats_ssize_type ssz2) {
  return (ssz1 != ssz2 ? ats_true_bool : ats_false_bool) ;
} /* end of [atspre_eq_ssize1_ssize1] */

/* ****** ****** */

#endif /* ATS_PRELUDE_SIZETYPE_CATS */

/* end of [sizetype.cats] */
