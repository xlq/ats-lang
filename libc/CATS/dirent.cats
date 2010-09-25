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

#ifndef ATS_LIBC_DIRENT_CATS
#define ATS_LIBC_DIRENT_CATS

/* ****** ****** */

#include <errno.h>
#include <sys/types.h>
#include <dirent.h>
#include <stdio.h> // for [perror]

/* ****** ****** */

#include "ats_types.h"

/* ****** ****** */

typedef DIR ats_DIR_type ;
typedef struct dirent ats_dirent_type ;

/* ****** ****** */

// implemented in [prelude/DATS/basics.dats]
extern ats_void_type
ats_exit_errmsg(ats_int_type n, ats_ptr_type msg) ;

// implemented in [prelude/CATS/printf.cats]
extern ats_void_type
atspre_exit_prerrf(ats_int_type code, ats_ptr_type fmt, ...) ;

/* ****** ****** */

ATSinline()
ats_ptr_type
atslib_dirent_d_name_get
  (ats_ptr_type dir) { return ((ats_dirent_type*)dir)->d_name ; }
// end of [atslib_dirent_d_name_get]

/* ****** ****** */

#define atslib_closedir_err closedir

ATSinline()
ats_void_type
atslib_closedir_exn (ats_ptr_type dir) {
  int err = closedir (dir) ; if (err < 0) {
    perror ("closedir") ;
    ats_exit_errmsg (errno, "Exit: [closedir] failed.\n") ;
  }
  return ;
} /* end of [atslib_closedir_exn] */

/* ****** ****** */

#define atslib_opendir_err opendir

ATSinline()
ats_ptr_type
atslib_opendir_exn (ats_ref_type path) {
  DIR* ret = opendir (path) ; if (!ret) {
    perror ("opendir") ;
    atspre_exit_prerrf (errno, "Exit: [opendir(%s)] failed.\n", path) ;
  }
  return ret ;
} /* end of [atslib_opendir_exn] */

/* ****** ****** */

#define atslib_readdir readdir

ATSinline()
ats_int_type
atslib_readdir_r_err (
  ats_ptr_type dir, ats_ref_type ent, ats_ref_type ret
) {
  int err = readdir_r (
    (DIR*)dir, (ats_dirent_type*)ent, (ats_dirent_type**)ret
  ) ;
  return err ;
} /* end of [atslib_readdir_r_err] */

/* ****** ****** */

#define atslib_rewinddir rewinddir 
#define atslib_seekdir seekdir
#define atslib_telldir telldir

/* ****** ****** */

#endif /* ATS_LIBC_DIRENT_CATS */
