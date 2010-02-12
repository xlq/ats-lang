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
#include <sys/wait.h> // for [wait]
#include <unistd.h>

/* ****** ****** */

#include "ats_types.h"
// typedef pid_t ats_pid_type ;

/* ****** ****** */

// implemented in [prelude/DATS/basics.dats]
extern ats_void_type
ats_exit_errmsg(ats_int_type n, ats_ptr_type msg) ;

/* ****** ****** */

static inline
ats_pid_type
atslib_fork_exn () {
  pid_t pid ;
  pid = fork () ;
  if (pid < 0) {
    perror ("fork") ;
    ats_exit_errmsg (errno, "exit(ATS): [fork] failed.\n") ;
  } // end of [if]
  return pid ;
} /* end of [atslib_fork_exn] */

/* ****** ****** */

static inline
ats_pid_type
atslib_wait_with_status (
  ats_ptr_type p // for storing status
) {
  return wait((int*)p) ;
} // end of [atslib_wait_with_status]

static inline
ats_pid_type
atslib_wait_without_status () { return wait((int*)0) ; }
// end of [atslib_wait_without_status]

/* ****** ****** */

static inline
ats_int_type // n >= 0
atslib_sleep (ats_int_type n) { return sleep (n) ; }

static inline
ats_void_type // n >= 0
atslib_usleep (ats_int_type n) { usleep (n) ; return ; }

/* ****** ****** */

#define atslib_getpagesize getpagesize

/* ****** ****** */

#define atslib_getpid getpid
#define atslib_getppid getppid

#define atslib_getuid getuid
#define atslib_geteuid geteuid

/* ****** ****** */

#define atslib_chdir_err chdir

static inline
ats_void_type
atslib_chdir_exn (
  ats_ptr_type path
) {
  int err ;
  err = chdir ((char*)path) ;
  if (err == -1) {
    perror ("chdir") ;
    ats_exit_errmsg (1, "exit(ATS): [chdir] failed\n") ;
  } // end of [if]
} /* end of [atslib_chdir_exn] */

#define atslib_fchdir_err fchdir

static inline
ats_void_type
atslib_fchdir_exn
  (ats_int_type fd) {
  int err ;
  err = fchdir (fd) ;
  if (err == -1) {
    perror ("fchdir") ;
    ats_exit_errmsg (1, "exit(ATS): [fchdir] failed\n") ;
  } // end of [if]
} /* end of [atslib_fchdir_exn] */

/* ****** ****** */

#define atslib_link_err link

static inline
ats_void_type
atslib_link_exn (
  ats_ptr_type src, ats_ptr_type dst
) { 
  int err ;
  err = link ((char*)src, (char*)dst) ;
  if (err == -1) {
    perror ("link") ;
    ats_exit_errmsg (1, "exit(ATS): [link] failed\n") ;
  } // end of [if]
  return ;
} /* end of [atslib_link_exn] */

/* ****** ****** */

#define atslib_unlink_err unlink

static inline
ats_void_type
atslib_unlink_exn (ats_ptr_type path) { 
  int err ;
  err = unlink ((char*)path) ;
  if (err == -1) {
    perror ("unlink") ;
    ats_exit_errmsg (1, "exit(ATS): [unlink] failed\n") ;
  } // end of [if]
  return ;
} /* end of [atslib_unlink_exn] */

/* ****** ****** */

static inline
ats_off_type
atslib_fildes_lseek_err (
  ats_int_type fd
, ats_off_type ofs
, ats_int_type whence
) {
  return lseek(fd, ofs, whence) ;
} /* end of [atslib_fildes_lseek_err] */

static inline
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

static inline
ats_ssize_type
atslib_fildes_pread_err (
  ats_int_type fd
, ats_ptr_type buf
, ats_size_type cnt
, ats_off_type ofs
) {
  return pread(fd, buf, cnt, ofs) ;
} /* end of [atslib_fildes_pread_err] */

static inline
ats_ssize_type
atslib_fildes_pwrite_err (
  ats_int_type fd
, ats_ptr_type buf
, ats_size_type cnt
, ats_off_type ofs
) {
  return pwrite(fd, buf, cnt, ofs) ;
} /* end of [atslib_fildes_pwrite_err] */

/* ****** ****** */

static inline
ats_void_type
atslib_sync () { sync () ; return ; }
// end of [atslib_sync]

static inline
ats_int_type
atslib_fsync (ats_int_type fd) { return fsync (fd) ; }
// end of [atslib_fsync]

static inline
ats_int_type
atslib_fdatasync (ats_int_type fd) { return fdatasync (fd) ; }
// end of [atslib_fdatasync]

/* ****** ****** */

#endif /* ATS_LIBC_UNISTD_CATS */
