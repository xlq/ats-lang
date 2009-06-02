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

#ifndef ATS_LIBC_UNISTD_CATS
#define ATS_LIBC_UNISTD_CATS

/* ****** ****** */

#include <errno.h>
#include <sys/types.h>
#include <unistd.h>

/* ****** ****** */

#include "ats_types.h"
// typedef pid_t ats_pid_type ;

/* ****** ****** */

static inline
ats_pid_type atslib_fork_exn () {
  pid_t pid ;
  pid = fork () ;

  if (pid < 0) {
    ats_exit_errmsg (errno, "Exit: [fork] failed.\n") ;
  }
  return pid ;
}

/* ****** ****** */

static inline
ats_pid_type
atslib_wait_with_status (ats_ptr_type p) {
  return wait ((int *)p) ;
}

static inline
ats_pid_type
atslib_wait_without_status () {
  return wait ((int *)0) ;
}

/* ****** ****** */

static inline
ats_int_type // n >= 0
atslib_sleep (ats_int_type n) { return sleep (n) ; }

static inline
ats_void_type // n >= 0
atslib_usleep (ats_int_type n) { usleep (n) ; return ; }

/* ****** ****** */

static inline
ats_pid_type
atslib_getpid () { return getpid () ; }

static inline
ats_pid_type
atslib_getppid () { return getppid () ; }

/* ****** ****** */

static inline
ats_uid_type
atslib_getuid () { return getuid () ; }

static inline
ats_uid_type
atslib_geteuid () { return geteuid () ; }

/* ****** ****** */

static inline
ats_int_type
atslib_unlink_err (ats_ptr_type name) { return unlink ((char*)name) ; }
// end of [atslib_unlink_err]

/* ****** ****** */

static inline
ats_void_type
atslib_sync () { sync () ; return ; }
// end of [atslib_sync]

/* ****** ****** */

#endif /* ATS_LIBC_UNISTD_CATS */
