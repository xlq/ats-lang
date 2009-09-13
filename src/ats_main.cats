/***********************************************************************/
/*                                                                     */
/*                        Applied Type System                          */
/*                                                                     */
/*                             Hongwei Xi                              */
/*                                                                     */
/***********************************************************************/

/*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi.
**
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

// September 2008
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

/* ****** ****** */

#ifndef ATS_SRC_MAIN_CATS
#define ATS_SRC_MAIN_CATS

/* ****** ****** */

extern ats_void_type
ats_posmark_xref_flag_set (ats_ptr_type flag) ;

static inline
ats_main_is_posmark_xref_prefix (ats_ptr_type s0) {
  int cmp, n1, n2, ln ; char *s, *flag ;
  static char* POSMARK_XREF = "--posmark_xref" ;
  s = (char*)s0 ;
  n1 = strlen (POSMARK_XREF) ;
  cmp = strncmp (POSMARK_XREF, s, n1) ;
  if (cmp == 0) {
    n2 = strlen (s) ;
    if (s[n1] == '=') n1 += 1 ;
    ln = n2 - n1 ;
    if (ln > 0) {
      if (s[n2-1] == '/') { ln -= 1 ; }
      flag = ATS_MALLOC (ln + 2) ;
      strncpy (flag, &s[n1], ln) ;
      flag[ln] = '/' ; flag[ln+1] = '\000' ;
    } else {
      flag = "" ;
    } // end of [if]
/*
    fprintf (stderr, "ats_main_is_posmark_xref_prefix: flag = %s\n", flag) ;
*/
    ats_posmark_xref_flag_set (flag) ;
  } // end of [if]
  return (cmp == 0 ? ats_true_bool : ats_false_bool) ;
} /* end of [ats_main_is_posmark_xref_prefix] */

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

// global
char *ats_main_ATSHOME = NULL ; // no need for marking as a root
int ats_main_ATSHOME_length = 0;

ats_ptr_type
ats_main_ATSHOME_getenv_exn () {
 char *value0 ;
 value0 = getenv ("ATSHOME") ; // this value cannot be GCed
 if (!value0) {
   fprintf (stderr, "The environment variable ATSHOME is undefined.\n") ;
   exit (1) ;
 }
 ats_main_ATSHOME = value0 ; ats_main_ATSHOME_length = strlen (value0) ;
 return value0 ;
} /* end of [ats_main_ATSHOME_getenv_exn] */

/* ****** ****** */

// global
char *ats_main_ATSHOMERELOC = NULL ; // no need for marking as a root

ats_void_type
ats_main_ATSHOMERELOC_set () {
  ats_main_ATSHOMERELOC = getenv ("ATSHOMERELOC") ; // this value cannot be GCed
/*
  fprintf (stderr, "ats_main_ATSHOMERELOC_set: ATSHOMERELOC = %s\n", ats_main_ATSHOMERELOC) ;
*/
  return ;
}

/* ****** ****** */

#endif // [ATS_SRC_MAIN_CATS]

/* end of [ats_main.cats] */
