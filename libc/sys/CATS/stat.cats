/************************************************************************/
/*                                                                      */
/*                         Applied Type System                          */
/*                                                                      */
/*                              Hongwei Xi                              */
/*                                                                      */
/************************************************************************/

/*
** ATS - Unleashing the Power of Types!
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

#ifndef _LIBC_SYS_STAT_CATS
#define _LIBC_SYS_STAT_CATS

/* ****** ****** */

#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h> // for [perror]

/* ****** ****** */

#include "libc/sys/CATS/types.cats"

/* ****** ****** */

// [struct stat] is declared in <bits/stat.h>
typedef struct stat ats_stat_type ;

/* ****** ****** */
//
// HX: implemented in [prelude/DATS/basics.dats]
//
extern ats_void_type
ats_exit_errmsg(ats_int_type n, ats_ptr_type msg) ;

/* ****** ****** */

ATSinline()
ats_dev_type
atslib_stat_get_st_dev
  (ats_ptr_type buf) {
  return ((ats_stat_type*)buf)->st_dev ;
} // end of [atslib_stat_get_st_dev]

ATSinline()
ats_ino_type
atslib_stat_get_st_ino
  (ats_ptr_type buf) {
  return ((ats_stat_type*)buf)->st_ino ;
} // end of [atslib_stat_get_st_ino]

/* ****** ****** */

ATSinline()
ats_mode_type
atslib_stat_get_st_mode
  (ats_ptr_type buf) {
  return ((ats_stat_type*)buf)->st_mode ;
} // end of [atslib_stat_get_st_mode]

/* ****** ****** */

ATSinline()
ats_nlink_type
atslib_stat_get_st_nlink
  (ats_ptr_type buf) {
  return ((ats_stat_type*)buf)->st_nlink ;
} // end of [atslib_stat_get_st_nlink]

ATSinline()
ats_off_type
atslib_stat_get_st_size
  (ats_ptr_type buf) {
  return ((ats_stat_type*)buf)->st_size ;
} // end of [atslib_stat_get_st_size]

/* ****** ****** */

ATSinline()
ats_uid_type
atslib_stat_get_st_gid
  (ats_ptr_type buf) {
  return ((ats_stat_type*)buf)->st_gid ;
} // end of [atslib_stat_get_st_gid]

ATSinline()
ats_uid_type
atslib_stat_get_st_uid
  (ats_ptr_type buf) {
  return ((ats_stat_type*)buf)->st_uid ;
} // end of [atslib_stat_get_st_uid]

/* ****** ****** */

ATSinline()
ats_bool_type
atslib_S_ISBLK (ats_mode_type m) { return S_ISBLK(m) ; }

ATSinline()
ats_bool_type
atslib_S_ISCHR (ats_mode_type m) { return S_ISCHR(m) ; }

ATSinline()
ats_bool_type
atslib_S_ISDIR (ats_mode_type m) { return S_ISDIR(m) ; }

ATSinline()
ats_bool_type
atslib_S_ISFIFO (ats_mode_type m) { return S_ISFIFO(m) ; }

ATSinline()
ats_bool_type
atslib_S_ISREG (ats_mode_type m) { return S_ISREG(m) ; }

ATSinline()
ats_bool_type
atslib_S_ISLNK (ats_mode_type m) { return S_ISLNK(m) ; }

ATSinline()
ats_bool_type
atslib_S_ISSOCK (ats_mode_type m) { return S_ISSOCK(m) ; }

/* ****** ****** */

ATSinline()
ats_int_type
atslib_chmod_err (
  ats_ptr_type path, ats_mode_type mode
) {
  return chmod ((char*)path, mode) ;
} /* end of [atslib_chmod_err] */

ATSinline()
ats_void_type
atslib_chmod_exn (
  ats_ptr_type path, ats_mode_type mode
) {
  int err = chmod ((char*)path, mode) ; if (err < 0) {
    perror ("chmod"); ats_exit_errmsg (1, "exit(ATS): [chmod] failed.\n") ;
  }
  return ;
} /* end of [atslib_chmod_exn] */

/* ****** ****** */

ATSinline()
ats_int_type
atslib_mkdir_err (
  ats_ptr_type path, ats_mode_type mode
) {
   return mkdir ((char*)path, mode) ;
} /* end of [atslib_mkdir_err] */

ATSinline()
ats_void_type
atslib_mkdir_exn (ats_ptr_type path, ats_mode_type mode) {
  int err = mkdir ((char*)path, mode) ; if (err < 0) {
    perror ("mkdir"); ats_exit_errmsg (1, "exit(ATS): [mkdir] failed.\n") ;
  }
  return ;
} /* end of [atslib_mkdir_exn] */

/* ****** ****** */

ATSinline()
ats_int_type
atslib_stat_err (
  ats_ptr_type name, ats_ptr_type buf
) {
  return stat ((char*)name, (ats_stat_type*)buf) ;
} /* end of [atslib_stat_err] */

ATSinline()
ats_void_type
atslib_stat_exn (
  ats_ptr_type name, ats_ptr_type buf
) {
  int err ;
  err = stat ((char*)name, (ats_stat_type*)buf) ; if (err < 0) {
    perror ("stat"); ats_exit_errmsg (1, "exit(ATS): [stat] failed.\n") ;
  }
  return ;
} /* end of [atslib_stat_exn] */

/* ****** ****** */

ATSinline()
ats_int_type
atslib_lstat_err (
  ats_ptr_type name, ats_ptr_type buf
) {
  return lstat ((char*)name, (ats_stat_type*)buf) ;
} /* end of [atslib_lstat_err] */

ATSinline()
ats_void_type
atslib_lstat_exn (ats_ptr_type name, ats_ptr_type buf) {
  int err ;
  err = lstat ((char*)name, (ats_stat_type*)buf) ; if (err < 0) {
    perror ("lstat"); ats_exit_errmsg (1, "exit(ATS): [lstat] failed.\n") ;
  }
  return ;
} /* end of [atslib_lstat_exn] */

/* ****** ****** */

ATSinline()
ats_mode_type
atslib_umask (ats_mode_type mask_new) {
  return umask (mask_new) ; /* the original mask is returned */
} /* end of [atslib_umask] */

/* ****** ****** */

#endif /* end of [_LIBC_SYS_STAT_CATS] */

/* end of [stat.cats] */
