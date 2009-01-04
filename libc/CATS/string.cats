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

#ifndef ATS_LIBC_STRING_CATS
#define ATS_LIBC_STRING_CATS

/* ****** ****** */

#include <string.h>

/* ****** ****** */

static inline
ats_int_type
atslib_strcmp (ats_ptr_type str1, ats_ptr_type str2) {
  return strcmp(str1, str2) ;
} /* end of [atslib_strcmp] */

static inline
ats_int_type
atslib_substrcmp (
  ats_ptr_type str1, ats_int_type i1
, ats_ptr_type str2, ats_int_type i2
) {
  return strcmp((char*)str1+i1, (char*)str2+i2) ;
} /* end of [atslib_substrcmp] */

/* ****** ****** */

static inline
ats_int_type
atslib_strncmp (ats_ptr_type str1, ats_ptr_type str2, ats_int_type n) {
  return strncmp(str1, str2, n) ;
} /* end of [atslib_strncmp] */

static inline
ats_int_type
atslib_substrncmp (
  ats_ptr_type str1, ats_int_type i1
, ats_ptr_type str2, ats_int_type i2
, ats_int_type n) {
  return strncmp((char*)str1+i1, (char*)str2+i2, n) ;
} /* end of [atslib_substrncmp] */

/* ****** ****** */

#endif /* ATS_LIBC_STRING_CATS */

/* end of [string.cats] */
