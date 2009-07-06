/*
**
** An interface for ATS to interact with BLAS
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
**
** Time: Summer, 2009
**
*/

/* ****** ****** */

#ifndef ATS_LIBATS_GENMATRICES_CATS
#define ATS_LIBATS_GENMATRICES_CATS

/* ****** ****** */

static inline
ats_ptr_type
atslib_GEVEC_split_tsz (
  ats_ptr_type p_vec
, ats_int_type d
, ats_int_type i
, ats_size_type tsz
) {
  return ((char*)p_vec) + i * (d * tsz) ;
} /* end of [atslib_GEVEC_split_tsz] */

/* ****** ****** */

#endif /* ATS_LIBATS_GENMATRICES_CATS */

/* end of [genmatrices.cats] */
