/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
** ATS/Anairiats - Unleashing the Potential of Types!
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// February 2008

/* ****** ****** */
//
// HX: ats_solver_fm:
// A solver based on the FM approach for linear constraints
//
/* ****** ****** */

#ifndef ATS_SRC_SOLVER_FM_CATS
#define ATS_SRC_SOLVER_FM_CATS

/* ****** ****** */

#include "ats_intinf.cats"

/* ****** ****** */

typedef ats_mpz_ptr_type i0nt;

/* ****** ****** */

ATSinline()
i0nt
atsopt_solver_fm_i0nt_of_int
  (ats_int_type i)
{
  ats_ptr_type p = atspre_ptr_alloc_tsz (sizeof (ats_mpz_viewt0ype));
  atslib_mpz_init_set_int (p, i);
  return p;
}
// end of [atsopt_solver_fm_i0nt_of_int]

ATSinline()
i0nt
atsopt_solver_fm_i0nt_of_intinf
  (ats_mpz_ptr_type i)
{ return i ; }
// end of [atsopt_solver_fm_i0nt_of_intinf]

/* ****** ****** */

ATSinline()
ats_bool_type
atsopt_solver_fm_gt_i0nt_int
  (i0nt i0, ats_int_type i) {
  return atsopt_gt_intinf_int (i0, i) ;
} // end of [atsopt_solver_fm_gt_i0nt_int]

ATSinline()
ats_bool_type
atsopt_solver_fm_gte_i0nt_int (
  i0nt i0, ats_int_type i
) {
  return atsopt_gte_intinf_int (i0, i) ;
} // end of [atsopt_solver_fm_gte_i0nt_int]

ATSinline()
ats_bool_type
atsopt_solver_fm_lt_i0nt_int (
  i0nt i0, ats_int_type i
) {
  return atsopt_lt_intinf_int (i0, i) ;
} // end of [atsopt_solver_fm_lt_i0nt_int]

ATSinline()
ats_bool_type
atsopt_solver_fm_lte_i0nt_int (
  i0nt i0, ats_int_type i
) {
  return atsopt_lte_intinf_int (i0, i) ;
} // end of [atsopt_solver_fm_lte_i0nt_int]

ATSinline()
ats_bool_type
atsopt_solver_fm_eq_i0nt_int (
  i0nt i0, ats_int_type i
) {
  return atsopt_eq_intinf_int (i0, i) ;
} // end of [atsopt_solver_fm_eq_i0nt_int]

ATSinline()
ats_bool_type
atsopt_solver_fm_neq_i0nt_int (
  i0nt i0, ats_int_type i
) {
  return atsopt_neq_intinf_int (i0, i) ;
} // end of [atsopt_solver_fm_neq_i0nt_int]

//

ATSinline()
ats_bool_type
atsopt_solver_fm_gt_i0nt_i0nt (
  i0nt i1, i0nt i2
) {
  return atsopt_gt_intinf_intinf (i1, i2) ;
} // end of [atsopt_solver_fm_gt_i0nt_i0nt]

ATSinline()
ats_bool_type
atsopt_solver_fm_lt_i0nt_i0nt (
  i0nt i1, i0nt i2
) {
  return atsopt_lt_intinf_intinf (i1, i2) ;
} // end of [atsopt_solver_fm_lt_i0nt_i0nt]

//

ATSinline()
i0nt
atsopt_solver_fm_neg_i0nt
  (i0nt i) { return atsopt_neg_intinf (i) ; }
// end of [atsopt_solver_fm_neg_i0nt]

ATSinline()
i0nt
atsopt_solver_fm_add_i0nt_i0nt (
  i0nt i1, i0nt i2
) {
  return atsopt_add_intinf_intinf (i1, i2) ;
} // end of [atsopt_solver_fm_add_i0nt_i0nt]

ATSinline()
i0nt
atsopt_solver_fm_sub_i0nt_i0nt (
  i0nt i1, i0nt i2
) {
  return atsopt_sub_intinf_intinf (i1, i2) ;
} // end of [atsopt_solver_fm_sub_i0nt_i0nt]

ATSinline()
i0nt
atsopt_solver_fm_mul_i0nt_i0nt (
  i0nt i1, i0nt i2
) {
  return atsopt_mul_intinf_intinf (i1, i2) ;
} // end of [atsopt_solver_fm_mul_i0nt_i0nt]

ATSinline()
i0nt
atsopt_solver_fm_div_i0nt_i0nt (
  i0nt i1, i0nt i2
) {
  mpz_ptr ans = ATS_MALLOC (sizeof(ats_mpz_viewt0ype)) ;
  mpz_init (ans) ;
  mpz_tdiv_q (ans, i1, i2) ;
  return ans ;
} // end of [atsopt_solver_fm_div_i0nt_i0nt]

//

ATSinline()
i0nt
atsopt_solver_fm_succ_i0nt
  (i0nt i) {
  mpz_ptr ans = ATS_MALLOC (sizeof(ats_mpz_viewt0ype)) ;
  mpz_init (ans) ;
  mpz_add_ui (ans, i, 1) ;
  return ans ;
}
// end of [atsopt_solver_fm_succ_i0nt]

ATSinline()
i0nt
atsopt_solver_fm_pred_i0nt
  (i0nt i) {
  mpz_ptr ans = ATS_MALLOC (sizeof(ats_mpz_viewt0ype)) ;
  mpz_init (ans) ;
  mpz_sub_ui (ans, i, 1) ;
  return ans ;
}
// end of [atsopt_solver_fm_pred_i0nt]

//

ATSinline()
i0nt
atsopt_solver_fm_mod_i0nt_i0nt
  (i0nt i1, i0nt i2) {
  mpz_ptr ans = ATS_MALLOC (sizeof(ats_mpz_viewt0ype)) ;
  mpz_init (ans);
  mpz_tdiv_r (ans, i1, i2) ;
  return ans ;
} // end of [atsopt_solver_fm_mod_i0nt_i0nt]

ATSinline()
i0nt
atsopt_solver_fm_gcd_i0nt_i0nt (
  i0nt i1, i0nt i2
) {
  if (atsopt_lt_intinf_int (i1, 0)) {
    i1 = atsopt_neg_intinf (i1) ;
  }
  if (atsopt_lt_intinf_int (i2, 0)) {
    i2 = atsopt_neg_intinf (i2) ;
  }
  while (1) {
    if (atsopt_eq_intinf_int (i2, 0)) return i1;
    i0nt tmp = atsopt_solver_fm_mod_i0nt_i0nt (i1, i2) ;
    i1 = i2;
    i2 = tmp;
  }
  return 0 ; /* deadcode */
} // end of [atsopt_solver_fm_gcd_i0nt_i0nt]

//

ATSinline()
ats_void_type
atsopt_solver_fm_fprint_i0nt
  (ats_ptr_type out, i0nt i) {
  atslib_fprint_mpz (out, i) ;
} // end of [atsopt_solver_fm_fprint_i0nt]

/* ****** ****** */

ATSinline()
ats_ptr_type
atsopt_solver_fm_intvecptr_make_view_ptr
  (ats_ptr_type p) { return p ; }
// end of [atsopt_solver_fm_intvecptr_make_view_ptr]

ATSinline()
ats_void_type
atsopt_solver_fm_intvecptr_free (ats_ptr_type p) {
  ATS_FREE (p) ; return ;
}

/* ****** ****** */

ATSinline()
ats_ptr_type
atsopt_solver_fm_intvec_ptr_make
  (ats_int_type n) {
  i0nt zero = ATS_MALLOC (sizeof(ats_mpz_viewt0ype)) ;
  mpz_init_set_si (zero, 0) ;
  i0nt *p ;
  int i ;
  int nbytes = n * sizeof(i0nt) ;
  p = ATS_MALLOC (nbytes) ;
  for (i=0; i<n; ++i) {
    p[i] = zero ;
  }
  return p ;
} // end of [atsopt_solver_fm_intvec_ptr_make]

/* ****** ****** */

#endif // ATS_SRC_SOLVER_FM_CATS

/* end of [ats_solver_fm.cats] */

