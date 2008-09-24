/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi.
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
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
 */

/* ****** ****** */

// September 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

/* ****** ****** */

#ifndef ATS_SRC_MAIN_CATS
#define ATS_SRC_MAIN_CATS

/* ****** ****** */

static int the_IATS_wait = 0 ;

static inline
ats_void_type ats_main_IATS_wait_set () {
  the_IATS_wait = 1 ; return ;
}

static inline
ats_bool_type ats_main_IATS_wait_is_set () {
  return (the_IATS_wait ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_void_type ats_main_IATS_wait_clear () {
  the_IATS_wait = 0 ; return ;
}

/* ****** ****** */

ats_bool_type
ats_main_is_IATS_flag (ats_ptr_type s0) {
  char *s = (char*)s0 ;
  if (*s != '-') return ats_false_bool ;
  ++s ; if (*s != 'I') return ats_false_bool ;
  ++s ; if (*s != 'A') return ats_false_bool ;
  ++s ; if (*s != 'T') return ats_false_bool ;
  ++s ; if (*s != 'S') return ats_false_bool ;
  return ats_true_bool ; 
} /* end of [ats_main_is_IATS_flag] */

ats_ptr_type
ats_main_IATS_extract (ats_ptr_type s0) {
  int n ; char* s ;
  n = strlen ((char*)s0) ;
  n -= 5 ; if (n <= 0) return (ats_ptr_type)0 ;
  s = ATS_MALLOC (n + 1) ;
  memcpy (s, (char*)s0 + 5, n) ; s[n] = '\0' ;
  return s ;
} /* end of [ats_main_IATS_extract] */

/* ****** ****** */

char *ats_main_ATSHOME = NULL ;
int ats_main_ATSHOME_length = 0;

ats_ptr_type
ats_main_ATSHOME_getenv_exn () {
 char *value0 ;
 value0 = getenv ("ATSHOME") ;
 if (!value0) {
   fprintf (stderr, "The environment variable ATSHOME is undefined.\n") ;
   exit (1) ;
 }
 ats_main_ATSHOME = value0 ; ats_main_ATSHOME_length = strlen (value0) ;
 return value0 ;
} /* end of [ats_main_ATSHOME_getenv_exn] */

/* ****** ****** */

char *ats_main_ATSHOMERELOC = NULL ;

ats_void_type
ats_main_ATSHOMERELOC_set () {
  ats_main_ATSHOMERELOC = getenv ("ATSHOMERELOC") ; return ;
}

/* ****** ****** */

#endif // [ATS_SRC_MAIN_CATS]

/* end of [ats_main.cats] */
