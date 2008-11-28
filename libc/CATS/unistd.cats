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

#ifndef ATS_LIBC_UNISTD_CATS
#define ATS_LIBC_UNISTD_CATS

/* ****** ****** */

#include <errno.h>
#include <sys/types.h>
#include <unistd.h>

/* ****** ****** */

#include "ats_types.h"
typedef pid_t ats_pid_t_type ;

/* ****** ****** */

static inline
ats_pid_t_type
atslib_wait_with_status (ats_ptr_type p) {
  return wait ((int *)p) ;
}

static inline
ats_pid_t_type
atslib_wait_without_status () {
  return wait ((int *)0) ;
}

static inline
ats_void_type
atslib_usleep (ats_int_type n) {
  usleep (n) ; return ;
}

/* ****** ****** */

#endif /* ATS_LIBC_UNISTD_CATS */
