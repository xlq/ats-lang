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

#ifndef __STRING_CATS
#define __STRING_CATS

/* ****** ****** */

#include <stdio.h>
#include <string.h>

/* ****** ****** */

#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

static inline
ats_ptr_type
atspre_string1_of_string0 (const ats_ptr_type s) { return s ; }

static inline
ats_ptr_type
atspre_strbuf_of_string1 (const ats_ptr_type s) { return s ; }

static inline
ats_ptr_type
atspre_string1_of_strbuf (const ats_ptr_type s) { return s ; }

/* ****** ****** */

static inline
ats_bool_type
atspre_lt_strbuf_strbuf
  (const ats_ptr_type s1, const ats_ptr_type s2) {
  int i = strcmp ((char *)s1, (char *)s2) ;
  return (i < 0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
atspre_lte_strbuf_strbuf
  (const ats_ptr_type s1, const ats_ptr_type s2) {
  int i = strcmp ((char *)s1, (char *)s2) ;
  return (i <= 0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
atspre_gt_strbuf_strbuf
  (const ats_ptr_type s1, const ats_ptr_type s2) {
  int i = strcmp ((char *)s1, (char *)s2) ;
  return (i > 0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
atspre_gte_strbuf_strbuf
  (const ats_ptr_type s1, const ats_ptr_type s2) {
  int i = strcmp ((char *)s1, (char *)s2) ;
  return (i >= 0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
atspre_eq_strbuf_strbuf
  (const ats_ptr_type s1, const ats_ptr_type s2) {
  int i = strcmp ((char *)s1, (char *)s2) ;
/*
  fprintf (stdout, "ats_eq_strbuf_strbuf: s1 = %s and s2 = %s\n", s1, s2) ;
  fprintf (stdout, "ats_eq_strbuf_strbuf: i = %i\n", i) ;
*/
  return (i == 0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_bool_type
atspre_neq_strbuf_strbuf
  (const ats_ptr_type s1, const ats_ptr_type s2) {
  int i = strcmp ((char *)s1, (char *)s2) ;
  return (i != 0 ? ats_true_bool : ats_false_bool) ;
}

static inline
ats_int_type
atspre_compare_strbuf_strbuf
  (const ats_ptr_type s1, const ats_ptr_type s2)
{
  int i = strcmp ((char *)s1, (char *)s2) ;
  if (i < 0) return -1 ;
  if (i > 0) return  1 ;
  return 0 ;
}

// print functions

static inline
ats_void_type
atspre_fprint_string (const ats_ptr_type out, const ats_ptr_type s) {
  int n = fprintf ((FILE *)out, "%s", (char *)s) ;
  if (n < 0) {
    ats_exit_errmsg (n, (ats_ptr_type)"Exit: [fprint_string] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_string (const ats_ptr_type s) {
  atspre_stdout_view_get() ;
  atspre_fprint_string(stdout, s) ;
  atspre_stdout_view_set() ;
  return ;
}

static inline
ats_void_type
atspre_prerr_string (const ats_ptr_type s) {
  atspre_stderr_view_get() ;
  atspre_fprint_string(stderr, s) ;
  atspre_stderr_view_set() ;
  return ;
}

/* ****** ****** */

static inline
ats_ptr_type
atspre_strbuf_make_char
  (const ats_int_type n, const ats_char_type c) {
  char *p ; 
  p = ATS_MALLOC(n+1) ; memset (p, c, n) ; p[n] = '\000' ;
  return p ;
}

static inline
ats_ptr_type
atspre_strbuf_make_bufptr
  (const ats_ptr_type src0, const ats_int_type start, const ats_int_type len)
{
  char *des, *src ;

  des = ATS_MALLOC(len+1) ;
  src = ((char*)src0) + start ;

  memcpy(des, src, len) ; des[len] = '\000' ;
  return des ;
}

/* ****** ****** */

static inline
ats_void_type
atspre_strbuf_append (const ats_ptr_type s1, const ats_ptr_type s2) {
  strcat(s1, s2); return ;
}

static inline
ats_ptr_type
atspre_string_append (const ats_ptr_type s1, const ats_ptr_type s2) {
  int n1, n2 ;
  char *des ;

  n1 = strlen ((char *)s1) ;
  n2 = strlen ((char *)s2) ;
  des = ATS_MALLOC(n1+n2+1) ;
  des[n1+n2] = '\000' ;
  memcpy(des, s1, n1) ; memcpy (des+n1, s2, n2) ;
  return des ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_strbuf_contains
  (const ats_ptr_type s0, const ats_char_type c) {
  char *s = strchr((char*)s0, (char)c) ;
  return (s != (char*)0 ? ats_true_bool : ats_false_bool) ;
}

/* ****** ****** */

static inline
ats_int_type
atspre_strbuf_length (const ats_ptr_type s) {
  return (strlen((char *)s)) ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_strbuf_is_empty(const ats_ptr_type s) {
  return (*((char *)s) == '\000') ;
}

static inline
ats_bool_type
atspre_strbuf_is_not_empty(const ats_ptr_type s) {
  return (*((char *)s) != '\000') ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_strbuf_is_at_end (ats_ptr_type s, ats_int_type i) {
  return (*((char *)s + i) == '\000' ? ats_true_bool : ats_false_bool) ;
}

/* ****** ****** */

static inline
ats_char_type
atspre_strbuf_get_char_at
  (const ats_ptr_type s, const ats_int_type offset) {
  return *((char *)s + offset) ;
}

static inline
ats_void_type
atspre_strbuf_set_char_at
  (const ats_ptr_type s, const ats_int_type offset, const char c) {
  *((char *)s + offset) = c ; return ;
}

/* ****** ****** */

static inline
ats_int_type
atspre_strbuf_index_of_char_from_left
  (const ats_ptr_type s, const ats_char_type c) {
  char *res ;
  res = strchr ((char *)s, c) ;
  if (res != (char *)0) return (res - (char *)s) ;
  return (-1) ;
}

static inline
ats_int_type
atspre_strbuf_index_of_char_from_right
  (const ats_ptr_type s, const ats_char_type c) {
  char *res ;
  res = strrchr ((char *)s, c) ;
  if (res != (char *)0) return (res - (char *)s) ;
  return (-1) ;
}

/* ****** ****** */

static inline
ats_int_type
atspre_string_index_of_string
  (const ats_ptr_type s1, const ats_ptr_type s2) {
  char *res ;
  res = strstr ((char *)s1, (char *)s2) ;
  if (res != (char *)0) return (res - (char *)s1) ;
  return (-1) ;
}

/* ****** ****** */

static inline
ats_ptr_type
atspre_string_singleton (const ats_char_type c) {
  return atspre_tostring_char (c) ;
}

/* ****** ****** */

static /* inline */
ats_ptr_type
atspre_string_tolower (const ats_ptr_type s) {
  int n ;
  char *src, *des0, *des ;

  src = (char *)s ; n = strlen (src) ;
  des0 = ATS_MALLOC(n+1) ; des = des0 ;
  while (n > 0) { *des = tolower (*src) ; ++des ; ++src ; --n ; }
  *des = '\000' ;
  return des0 ;
}

static /* inline */
ats_ptr_type
atspre_string_toupper (const ats_ptr_type s) {
  int n ;
  char *src, *des0, *des ;

  src = (char *)s ; n = strlen (src) ;
  des0 = ATS_MALLOC(n+1) ; des = des0 ;
  while (n > 0) { *des = toupper (*src) ; ++des ; ++src ; --n ; }
  *des = '\000' ;
  return des0 ;
}

/* ****** ****** */

// functions for optional strings

static
ats_ptr_type atspre_stropt_none = (ats_ptr_type)0 ;

static inline
ats_ptr_type
atspre_stropt_some (const ats_ptr_type s) { return s ; }

static inline
ats_ptr_type
atspre_stropt_unsome (const ats_ptr_type s) { return s ; }

static inline
ats_bool_type
atspre_stropt_is_none (const ats_ptr_type s) {
  return (s == (ats_ptr_type)0) ;
}

static inline
ats_bool_type
atspre_stropt_is_some (const ats_ptr_type s) {
  return (s != (ats_ptr_type)0) ;
}

/* ****** ****** */

#endif /* __STRING_CATS */
