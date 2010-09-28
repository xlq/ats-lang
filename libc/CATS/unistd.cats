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
** Copyright (C) 2002-2010 Hongwei Xi.
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
#include <sys/wait.h> // for [wait]
#include <unistd.h>

/* ****** ****** */

#include "libc/sys/CATS/types.cats" // for [pid_t]

/* ****** ****** */

// implemented in [prelude/DATS/basics.dats]
extern ats_void_type
ats_exit_errmsg(ats_int_type n, ats_ptr_type msg) ;

/* ****** ****** */

ATSinline()
ats_pid_type
atslib_fork_exn () {
  pid_t pid ;
//
  pid = fork () ;
//
  if (pid < 0) {
    perror ("fork") ;
    ats_exit_errmsg (errno, (ats_ptr_type)"exit(ATS): [fork] failed.\n") ;
    // end of [ats_exit_errmsg]
  } // end of [if]
//
  return pid ;
} // end of [atslib_fork_exn]

/* ****** ****** */

#define atslib_getcwd getcwd

/* ****** ****** */

ATSinline()
ats_pid_type
atslib_wait_with_status (
  ats_ptr_type p // for storing status
) {
  return wait((int*)p) ;
} // end of [atslib_wait_with_status]

ATSinline()
ats_pid_type
atslib_wait_without_status () { return wait((int*)0) ; }
// end of [atslib_wait_without_status]

/* ****** ****** */

#define atslib_sleep sleep

ATSinline()
ats_void_type // n >= 0
atslib_usleep (ats_int_type n) { usleep (n) ; return ; }

/* ****** ****** */

#define atslib_getpagesize getpagesize

/* ****** ****** */

#define atslib_getpid getpid
#define atslib_getppid getppid

#define atslib_getuid getuid
#define atslib_geteuid geteuid

#define atslib_getlogin getlogin

/* ****** ****** */

#define atslib_chdir chdir
#define atslib_fchdir fchdir

/* ****** ****** */

#define atslib_link link
#define atslib_unlink unlink

/* ****** ****** */

#define atslib_fildes_lseek_err lseek

ATSinline()
ats_off_type
atslib_fildes_lseek_exn (
  ats_int_type fd
, ats_off_type ofs
, ats_int_type whence
) {
  off_t ofs_new ;
  ofs_new = lseek(fd, ofs, whence) ;
  if (ofs_new == (ats_off_type)(-1)) {
    perror ("lseek") ;
    ats_exit_errmsg (1, "exit(ATS): [lseek] failed\n") ;
  }
  return ofs_new ;
} /* end of [atslib_fildes_lseek_exn] */

/* ****** ****** */

#define atslib_fildes_pread pread
#define atslib_fildes_pwrite pwrite

/* ****** ****** */

#define atslib_sync sync
#define atslib_fsync fsync
#define atslib_fdatasync fdatasync

/* ****** ****** */

#define atslib_pathconf pathconf
#define atslib_fpathconf fpathconf

/* ****** ****** */

#define atslib_readlink readlink

/* ****** ****** */

#define atslib_setsid setsid
#define atslib_getsid getsid
#define atslib_setpgid setpgid
#define atslib_getpgid getpgid

/* ****** ****** */

#define atslib_tcsetpgrp tcsetpgrp
#define atslib_tcgetpgrp tcgetpgrp

/* ****** ****** */

#endif /* ATS_LIBC_UNISTD_CATS */

/* end of [unistd.cats] */
