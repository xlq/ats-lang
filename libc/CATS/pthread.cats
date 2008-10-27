/* ******************************************************************* */
/*                                                                      /
/*                         Applied Type System                          /
/*                                                                      /
/*                              Hongwei Xi                              /
/*                                                                      /
/* ******************************************************************* */

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

/* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) */

/*
** A linker error is issued if a user does not define multithread and
** tries to use them anyways
*/

/* ****** ****** */

#ifndef _LIBC_PTHREAD_CATS
#define _LIBC_PTHREAD_CATS

#ifdef _ATS_MULTITHREAD

// #define THREAD_SAFE ?

#include <pthread.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

//

#include "ats_basics.h"

//

/* ****** ****** */

static inline
ats_void_type
atslib_pthread_mutex_init_locked (ats_ptr_type p) {
  pthread_mutex_init ((pthread_mutex_t*)p, NULL) ;
  pthread_mutex_lock ((pthread_mutex_t*)p) ;
  return ;
}

static inline
ats_void_type
atslib_pthread_mutex_init_unlocked (ats_ptr_type p) {
  pthread_mutex_init ((pthread_mutex_t*)p, NULL) ; return ;
}

/* ****** ****** */

static inline
ats_ptr_type
atslib_pthread_mutex_create_locked (void) {
  pthread_mutex_t *p ;
  p = (pthread_mutex_t*)ATS_MALLOC(sizeof (pthread_mutex_t)) ;
  pthread_mutex_init_locked (p, NULL) ;
  return p ;
}

static inline
ats_ptr_type
atslib_pthread_mutex_create_unlocked (void) {
  pthread_mutex_t *p ;
  p = (pthread_mutex_t*)ATS_MALLOC(sizeof (pthread_mutex_t)) ;
  pthread_mutex_init_unlocked (p, NULL) ;
  return p ;
}

/* ****** ****** */

static inline
ats_void_type
atslib_pthread_mutex_lock (ats_ptr_type mutex) {
  pthread_mutex_lock ((pthread_mutex_t*)mutex) ; return ;
}

static inline
ats_void_type
atslib_pthread_mutex_unlock (ats_ptr_type mutex) {
  pthread_mutex_unlock ((pthread_mutex_t*)mutex) ; return ;
}

/* ****** ****** */

static inline
ats_ptr_type
atslib_pthread_cond_create (void) {
  pthread_cond_t *p ;
  p = (pthread_cond_t*)ATS_MALLOC(sizeof (pthread_cond_t)) ;
  pthread_cond_init (p, NULL) ;
  return p ;
}

static inline
ats_void_type
atslib_pthread_cond_wait_mutex
  (ats_ptr_type cond, ats_ptr_type mutex) {
  pthread_cond_wait ((pthread_cond_t*)cond, (pthread_mutex_t*)mutex) ;
  return ;
}

static inline
ats_void_type
atslib_pthread_cond_signal (ats_ptr_type cond) {
  pthread_cond_signal ((pthread_cond_t*)cond) ; return ;
}

static inline
ats_void_type
atslib_pthread_cond_broadcast (ats_ptr_type cond) {
  pthread_cond_broadcast ((pthread_cond_t*)cond) ; return ;
}

/* ****** ****** */

#endif /* [ifdef _ATS_MULTITHREAD] */

/* ****** ****** */

#endif /* _LIBC_PTHREAD_CATS */

/* end of [pthread.cats] */
