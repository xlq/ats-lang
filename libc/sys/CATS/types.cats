/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
 * ATS - Unleashing the Power of Types!
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

#ifndef _LIBC_SYS_TYPES_CATS
#define _LIBC_SYS_TYPES_CATS

/* ****** ****** */

#include <time.h>
#include <sys/types.h>

// typedef blksize_t ats_blksize_type ; // I/O block size

typedef blkcnt_t ats_blkcnt_type ; // number of blocks allowed

// it should be defined in [sys/types.h] but it is actually in [time.h]
typedef clock_t ats_clock_type ; // for CLOCKS_PER_SEC

// not supported on Mac OSX ?
// typedef clockid_t ats_clockid_type ; // for clock ID type

typedef dev_t ats_dev_type ; // for device IDs

typedef fsblkcnt_t ats_fsblkcnt_type ; // file system block counts

typedef fsfilcnt_t ats_fsfilcnt_type ; // file system file counts

typedef gid_t ats_gid_type ; // for group IDs

typedef ino_t ats_ino_type ; // for file serial numbers

typedef key_t ats_key_type ; // for XSI interprocess communication

typedef mode_t ats_mode_type ; // file mode

typedef nlink_t ats_nlink_type ; // number of hard links to a file

/* ****** ****** */

typedef off_t ats_off_type ; // file size in bytes

static inline
ats_lint_type atslib_lint_of_off (ats_off_type off) {
  return off ;
}

/* ****** ****** */

typedef pid_t ats_pid_type ; // for process IDs // signed integer type

static inline
ats_int_type atslib_int_of_pid (ats_pid_type p) { return p ; }
/* end of [atslib_int_of_pid] */

/* ****** ****** */

// already defined in [ats_types.h]
// typedef size_t ats_size_type ; // for sizes of objects
// typedef ssize_t ats_ssize_type ; // for sizes or error indication

typedef time_t ats_time_type ; // for time in seconds

// not supported on Mac OSX ?
// typedef timer_t ats_timer_type ; // for timers returned by timer_create ()
// typedef useconds_t ats_useconds_type ; // for time in microseconds

/* ****** ****** */

typedef uid_t ats_uid_type ;

static inline
ats_int_type atslib_int_of_uid (ats_uid_type u) { return u ; }
/* end of [atslist_int_of_uid] */

static inline
ats_uid_type atslib_uid_of_int (ats_int_type i) { return i ; }
/* end of [atslist_uid_of_int] */

/* ****** ****** */

#endif /* end of [_LIBC_SYS_TYPES_CATS] */

/* end of [types.cats] */
