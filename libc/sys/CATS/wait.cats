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
** Copyright (C) 2002-2009 Hongwei Xi.
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

#ifndef _LIBC_SYS_WAIT_CATS
#define _LIBC_SYS_WAIT_CATS

#include <sys/types.h>
#include <sys/wait.h>

/* ****** ****** */

#include "libc/sys/CATS/types.cats"

/* ****** ****** */

static inline
ats_int_type
atslib_WIFEXITED (ats_int_type status) { return WIFEXITED(status) ; }
// end of [atslib_WIFEXITED]

static inline
ats_int_type
atslib_WEXITSTATUS
  (ats_int_type status) { return WEXITSTATUS(status) ; }
// end of [atslib_WEXITSTATUS]

/* ****** ****** */

static inline
ats_int_type
atslib_WIFSIGNALED (ats_int_type status) { return WIFSIGNALED(status) ; }
// end of [atslib_WIFSIGNALED]

static inline
ats_int_type
atslib_WTERMSIG
  (ats_int_type status) { return WTERMSIG(status) ; }
// end of [atslib_WTERMSIG]

/* ****** ****** */

static inline
ats_int_type
atslib_WIFSTOPPED (ats_int_type status) { return WIFSTOPPED(status) ; }
// end of [atslib_WIFSTOPPED]

static inline
ats_int_type
atslib_WSTOPSIG
  (ats_int_type status) { return WSTOPSIG(status) ; }
// end of [atslib_WSTOPSIG]

/* ****** ****** */

static inline
ats_pid_type
atslib_wait
  (ats_ref_type status) { return wait ((int*)status) ; }
/* end of [atslib_wait] */

static inline
ats_pid_type
atslib_waitpid (
  ats_pid_type chldpid
, ats_ref_type status
, ats_int_type options
) { 
  return waitpid ((pid_t)chldpid, (int*)status, (int)options) ;
} /* end of [atslib_waitpid] */

/* ****** ****** */

#endif /* end of [_LIBC_SYS_WAIT_CATS] */

/* end of [wait.cats] */
