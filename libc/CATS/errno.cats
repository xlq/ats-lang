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

#ifndef ATS_LIBC_ERRNO_CATS
#define ATS_LIBC_ERRNO_CATS

/* ****** ****** */

#include <errno.h>

/* ****** ****** */

static inline
ats_int_type
atslib_errno_get () { return errno ; }
// end of [atslib_errno_get]

static inline
ats_void_type
atslib_errno_set (ats_int_type n) { errno = n ; return ; }
// end of [atslib_errno_set]

static inline
ats_void_type
atslib_errno_reset () { errno = 0/*ENONE*/ ; return ; }
// end of [atslib_errno_reset]

/* ****** ****** */

static inline
ats_bool_type
atslib_eq_errno_errno
  (ats_int_type n1, ats_int_type n2) {
  return (n1 == n2 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
atslib_neq_errno_errno
  (ats_int_type n1, ats_int_type n2) {
  return (n1 != n2 ? ats_true_bool : ats_false_bool) ;
}

/* ****** ****** */

#endif /* ATS_LIBC_ERRNO_CATS */

/* end of [time.cats] */
