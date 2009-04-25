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
**
*/

/* ****** ****** */

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/* ****** ****** */

#ifndef ATS_LIBC_STRINGS_CATS
#define ATS_LIBC_STRINGS_CATS

/* ****** ****** */

#include <strings.h>

/* ****** ****** */

static inline
ats_int_type
atslib_ffs (ats_int_type i) { return ffs(i) ; }

/* ****** ****** */

static inline
ats_int_type
atslib_strcasecmp
  (ats_ptr_type s1, ats_ptr_type s2) {
  return strcasecmp ((char*)s1, (char*)s2) ;
} /* end of [atslib_strcasecmp] */

static inline
ats_int_type
atslib_strncasecmp
  (ats_ptr_type s1, ats_ptr_type s2, ats_size_type n) {
  return strncasecmp ((char*)s1, (char*)s2, (size_t)n) ;
} /* end of [atslib_strncasecmp] */

/* ****** ****** */

#endif /* ATS_LIBC_STRINGS_CATS */

/* end of [strings.cats] */
