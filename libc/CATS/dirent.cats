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

#ifndef ATS_LIBC_DIRENT_CATS
#define ATS_LIBC_DIRENT_CATS

/* ****** ****** */

#include <errno.h>
#include <sys/types.h>
#include <dirent.h>

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

typedef DIR ats_DIR_type ;
typedef struct dirent ats_dirent_type ;

/* ****** ****** */

static inline
ats_int_type
atslib_closedir_err (ats_ptr_type dir) {
  return closedir (dir) ;
}

static inline
ats_void_type
atslib_closedir_exn (ats_ptr_type dir) {
  int err = closedir (dir) ; if (err < 0) {
    perror ("closedir") ;
    ats_exit_errmsg (errno, "Exit: [closedir] failed.\n") ;
  }
  return ;
} /* atslib_closedir_exn */

/* ****** ****** */

static inline
ats_ptr_type
atslib_opendir_err (ats_ptr_type path) { return opendir (path) ; }

static inline
ats_ptr_type
atslib_opendir_exn (ats_ptr_type path) {
  DIR* ret = opendir (path) ; if (!ret) {
    perror ("opendir") ;
    atspre_exit_prerrf (errno, "Exit: [opendir(%s)] failed.\n", path) ;
  }
  return ret ;
} /* atslib_opendir_exn */

/* ****** ****** */

static inline
ats_ptr_type
atslib_readdir_err (ats_ptr_type dir) { return readdir ((DIR*)dir) ; }

static inline
ats_ptr_type
atslib_readdir_exn (ats_ptr_type dir) {
  struct dirent *ret = readdir ((DIR*)dir) ;
  if (!ret) {
    perror ("readdir") ;
    atspre_exit_prerrf (errno, "Exit: [readdir] failed.\n") ;
  }
  return ret ;
} /* atslib_readdir_exn */

/* ****** ****** */

#endif /* ATS_LIBC_DIRENT_CATS */
