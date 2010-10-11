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

#ifndef ATS_LIBC_STRING_CATS
#define ATS_LIBC_STRING_CATS

/* ****** ****** */

#include <string.h>

/* ****** ****** */

ATSinline()
ats_int_type
atslib_strcmp (
  ats_ptr_type str1, ats_ptr_type str2
) {
  return strcmp(str1, str2) ;
} /* end of [atslib_strcmp] */

ATSinline()
ats_int_type
atslib_substrcmp (
  ats_ptr_type str1, ats_size_type i1
, ats_ptr_type str2, ats_size_type i2
) {
  return strcmp((char*)str1+i1, (char*)str2+i2) ;
} /* end of [atslib_substrcmp] */

/* ****** ****** */

ATSinline()
ats_int_type
atslib_strncmp (
  ats_ptr_type str1, ats_ptr_type str2, ats_size_type n
) {
  return strncmp(str1, str2, n) ;
} /* end of [atslib_strncmp] */

ATSinline()
ats_int_type
atslib_substrncmp (
  ats_ptr_type str1, ats_size_type i1
, ats_ptr_type str2, ats_size_type i2
, ats_size_type n) {
  return strncmp((char*)str1+i1, (char*)str2+i2, n) ;
} // end of [atslib_substrncmp]

/* ****** ****** */

#define atslib_strlen strlen

/* ****** ****** */

#define atslib_strchr strchr // HX: no interface in ATS
#define atslib_strrchr strrchr // HX: no interface in ATS
#define atslib_strstr strstr // HX: no interface in ATS

/* ****** ****** */

#define atslib_strspn strspn
#define atslib_strcspn strcspn

/* ****** ****** */

#define atslib_strcpy strcpy
#define atslib_strcat strcat
#define atslib_strncat strncat // HX: no interface in ATS

/* ****** ****** */

ATSinline()
ats_ptr_type
atslib_strpbrk (
  ats_ptr_type buf, ats_ptr_type accept
) {
  return strpbrk((char*)buf, (char*)accept) ;
} // end of [atslib_strpbrk]

/* ****** ****** */

ATSinline()
ats_ptr_type
atslib_memchr (
  ats_ptr_type buf, ats_int_type chr, ats_size_type n
) {
  return memchr((void*)buf, (int)chr, (size_t)n) ;
} // end of [atslib_memchr]

/* ****** ****** */

ATSinline()
ats_int_type
atslib_memcmp (
  ats_ptr_type buf1, ats_ptr_type buf2, ats_size_type n
) {
  return memcmp((void*)buf1, (void*)buf2, (size_t)n) ;
} // end of [atslib_memcmp]

/* ****** ****** */

ATSinline()
ats_ptr_type
atslib_memcpy (
  ats_ptr_type dst, ats_ptr_type src, ats_size_type n
) {
  return memcpy((void*)dst, (void*)src, (size_t)n) ;
} // end of [atslib_memcpy]

/* ****** ****** */

ATSinline()
ats_ptr_type
atslib_memset (
  ats_ptr_type buf, ats_int_type chr, ats_size_type n
) {
  return memset((void*)buf, (int)chr, (size_t)n) ;
} // end of [atslib_memset]

/* ****** ****** */

#define atslib_strerror strerror

#if (0) // this one is commented out

ATSinline()
ats_int_type
atslib_strerror_r (
  ats_int_type errno
, ats_ptr_type buf
, ats_size_type bsz
) {
  return strerror_r(errno, (char*)buf, bsz) ;
} // end of [atslib_strerror_r]

#endif // end of [#if(0)]

/* ****** ****** */

#endif /* ATS_LIBC_STRING_CATS */

/* end of [string.cats] */
