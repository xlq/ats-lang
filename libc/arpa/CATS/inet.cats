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

#ifndef ATS_LIBC_ARPA_INET_CATS
#define ATS_LIBC_ARPA_INET_CATS

/* ****** ****** */

#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdio.h> // for [perror]

/* ****** ****** */

// implemented in [prelude/DATS/basics.dats]
extern ats_void_type
ats_exit_errmsg(ats_int_type n, ats_ptr_type msg) ;

/* ****** ****** */

static inline
ats_void_type
atslib_inet_aton_string_exn (ats_ptr_type cp, ats_ref_type inp) {
  int err = inet_aton((char*)cp, (in_addr_struct_t*)inp) ;
  if (err < 0) {
    perror ("inet_aton"); ats_exit_errmsg(1, "Exit: [inet_aton] failed.\n");
  }
  return ;
} /* end of [atslib_inet_aton_string_exn] */

static inline
ats_ptr_type // this function is not reentrant
atslib_inet_ntoa (in_addr_struct_t inp) { return inet_ntoa(inp) ; }

/* ****** ****** */

#endif /* end of [ATS_LIBC_ARPA_INET_CATS] */

/* end of [in.cats] */
