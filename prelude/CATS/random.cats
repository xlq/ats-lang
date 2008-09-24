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
 * Copyright (C) 2002-2008 Hongwei Xi
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

#ifndef __RANDOM_CATS
#define __RANDOM_CATS

/* ****** ****** */

#include <stdlib.h> // for randomization functions
#include <time.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

static inline
ats_void_type ats_srand48 (ats_lint_type seed) {
  srand48 ((long int)seed) ;
  return ;
}

static inline
ats_void_type ats_srand48_with_time () {
  srand48 ((long int)(time ((time_t *)0))) ;
  return ;
}

/* ****** ****** */

static inline
ats_double_type ats_drand48() {
  return (ats_double_type)(drand48()) ;
}

static inline
ats_lint_type ats_lrand48() {
  return (ats_lint_type)(lrand48()) ;
}

static inline
ats_lint_type ats_mrand48() {
  return (ats_lint_type)(mrand48()) ;
}

/* ****** ****** */

#endif /* __RANDOM_CATS */

/* end of [random.cats] */
