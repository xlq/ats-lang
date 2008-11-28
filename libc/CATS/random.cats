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

#ifndef ATS_LIBC_RANDOM_CATS
#define ATS_LIBC_RANDOM_CATS

/* ****** ****** */

#include <stdlib.h>
#include <time.h>

#include "ats_types.h"

/* ****** ****** */

static inline
ats_void_type
atslib_srand48 (ats_lint_type seed) {
  srand48 ((long int)seed) ;
  return ;
}

static inline
ats_void_type
atslib_srand48_with_time () {
  srand48 ((long int)(time ((time_t*)0))) ;
  return ;
}

/* ****** ****** */

static inline
ats_double_type
atslib_drand48 () { return drand48() ; }

static inline
ats_lint_type
atslib_lrand48 () { return lrand48() ; }

static inline
ats_lint_type
atslib_mrand48 () { return mrand48() ; }

/* ****** ****** */

static inline
ats_int_type // [n] is assumed to be positive!
atslib_randint (ats_int_type n) { return (lrand48 () % n) ; }

/* ****** ****** */

#endif /* ATS_LIBC_RANDOM_CATS */

/* end of [random.cats] */
