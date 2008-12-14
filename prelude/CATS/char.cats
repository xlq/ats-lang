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

#ifndef ATS_PRELUDE_CHAR_CATS
#define ATS_PRELUDE_CHAR_CATS

/* ****** ****** */

#include <ctype.h>
#include <stdio.h>

/* ****** ****** */

#include "ats_memory.h"
#include "ats_types.h"

/* ****** ****** */

static inline
ats_char_type
atspre_char_of_char (const ats_char_type c) { return c ; }

/* ****** ****** */

static inline
ats_char_type
atspre_char_of_uchar (const ats_uchar_type c) { return c ; }

static inline
ats_char_type
atspre_uchar_of_char (const ats_char_type c) { return c ; }

/* ****** ****** */

static inline
ats_char_type
atspre_char_of_int (const ats_int_type i) { return i ; }

/* ****** ****** */

#define atspre_char1_of_char atspre_char_of_char
#define atspre_char1_of_int atspre_char_of_int

/* ****** ****** */

static inline
ats_int_type
atspre_sub_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  return (c1 - c2) ;
} /* end of [atspre_sub_char_char] */

/* ****** ****** */

static inline
ats_bool_type
atspre_lt_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  return (c1 < c2) ;
}

static inline
ats_bool_type
atspre_lte_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  return (c1 <= c2) ;
}

static inline
ats_bool_type
atspre_gt_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  return (c1 > c2) ;
}

static inline
ats_bool_type
atspre_gte_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  return (c1 >= c2) ;
}

static inline
ats_bool_type
atspre_eq_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  return (c1 == c2) ;
}

static inline
ats_bool_type
atspre_neq_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  return (c1 != c2) ;
}

static inline
ats_int_type
atspre_compare_char_char
  (const ats_char_type c1, const ats_char_type c2) {
  int i = c1 - c2 ;
  if (i > 0) return  1 ;
  if (i < 0) return -1 ;
  return 0 ;
} /* end of [atspre_compare_char_char] */

// print functions

static inline
ats_void_type
atspre_fprint_char (const ats_ptr_type out, const ats_char_type c) {
  int n = fputc ((unsigned char)c, (FILE *)out) ;
  if (n < 0) {
    ats_exit_errmsg (n, "Exit: [fprint_char] failed.\n") ;
  }
  return ;
}

static inline
ats_void_type
atspre_print_char (const ats_char_type c) {
  atspre_stdout_view_get () ;
  atspre_fprint_char(stdout, c) ;
  atspre_stdout_view_set () ;
  return ;
}

static inline
ats_void_type
atspre_prerr_char (const ats_char_type c) {
  atspre_stderr_view_get () ;
  atspre_fprint_char(stderr, c) ;
  atspre_stderr_view_set () ;
  return ;
}

// stringization

static inline
ats_ptr_type
atspre_tostring_char (const ats_char_type c) {
  char *p ;
  p = (char *)ATS_MALLOC(2) ;
  *p = (char)c ; *(p+1) = '\000' ;
  return p ;
}

/* ****** ****** */

static inline
ats_bool_type
atspre_char_isalnum (const ats_char_type c) {
 return isalnum ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isalpha (const ats_char_type c) {
 return isalpha ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isascii (const ats_char_type c) {
 return isascii ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isblank (const ats_char_type c) {
 return isblank ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_iscntrl (const ats_char_type c) {
 return iscntrl ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isdigit (const ats_char_type c) {
 return isdigit ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isgraph (const ats_char_type c) {
 return isgraph ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_islower (const ats_char_type c) {
 return islower ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isprint (const ats_char_type c) {
 return isprint ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_ispunct (const ats_char_type c) {
 return ispunct ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isspace (const ats_char_type c) {
 return isspace ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_isupper (const ats_char_type c) {
 return isupper ((unsigned char)c) ;
}

static inline
ats_bool_type
atspre_char_ixdigit (const ats_char_type c) {
 return isxdigit ((unsigned char)c) ;
}

/* ****** ****** */

static inline
ats_char_type
atspre_char_toupper (const ats_char_type c) {
  return toupper ((unsigned char)c) ;
}

static inline
ats_char_type
atspre_char_tolower (const ats_char_type c) {
  return tolower ((unsigned char)c) ;
}

/* ****** ****** */

#endif /* ATS_PRELUDE_CHAR_CATS */

/* end of [char.cats] */
