/*
**
** An interface for ATS to interact with BLAS and LAPACK
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Contributed by Shivkumar Chandrasekaran (shiv AT ece DOT ucsb DOT edu)
**
** Time: Summer, 2009
**
*/

/* ****** ****** */

#ifndef ATS_LIBATS_FMATRIX_CATS
#define ATS_LIBATS_FMATRIX_CATS

/* ****** ****** */

static inline
ats_ptr_type
atslib_fmatrix_ptr_takeout_tsz (
  ats_ptr_type base
, ats_int_type i
, ats_int_type m
, ats_int_type j
, ats_size_type tsz
) {
  // the representation is column-major
  return ((char*)base) + (i + j * m) * tsz ;
} /* end of [atslib_fmatrix_ptr_takeout_tsz] */

/* ****** ****** */

#endif /* [ATS_LIBATS_FMATRIX_CATS] */

/* end of [fmatrix.cats] */

