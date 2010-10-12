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

#ifndef ATS_LIBC_SOCKET_CATS
#define ATS_LIBC_SOCKET_CATS

/* ****** ****** */

#include <errno.h>
#include <stdio.h> // for [perror]
#include <netinet/in.h>
#include <sys/un.h>

/* ****** ****** */

#include <sys/socket.h>

/* ****** ****** */

#include "libc/CATS/fcntl.cats"

/* ****** ****** */

// HX: [memset] is in [string.h]
extern void *memset(void *s, int c, size_t n);
// HX: implemented in [prelude/DATS/basics.dats]
extern ats_void_type
ats_exit_errmsg(ats_int_type n, ats_ptr_type msg) ;

/* ****** ****** */

typedef int socket_type_t ;
typedef int address_family_t ;

/* ****** ****** */

ATSinline()
ats_int_type
atslib_socket_family_type_err (
  address_family_t af, socket_type_t st
) {
  return socket(af, st, 0) ;
} // end of [atslib_socket_family_type_err]

ATSinline()
ats_int_type
atslib_socket_family_type_exn (
  address_family_t af, socket_type_t st
) {
  int res ;
  res = socket(af, st, 0) ;
  if (res < 0) {
    perror("socket");
    ats_exit_errmsg(
      EXIT_FAILURE, (ats_ptr_type)"exit(ATS): [socket] failed.\n"
    ) ;
  }
  return res ;
} // end of [atslib_socket_family_type_exn]

/* ****** ****** */

ATSinline()
ats_void_type
atslib_sockaddr_ipv4_init (
  ats_ptr_type sa0
, address_family_t af
, in_addr_t inp
, in_port_t port
) {
  struct sockaddr_in *sa = sa0 ;
  memset(sa, 0, sizeof (struct sockaddr_in)) ;
  sa->sin_family = af ;
  sa->sin_addr.s_addr = inp ;
  sa->sin_port = port ;
} // end of [sockaddr_ipv4_init]

/* ****** ****** */

#define atslib_connect_err connect

/* ****** ****** */

#define atslib_bind_err bind

ATSinline()
ats_void_type
atslib_bind_exn (
  ats_int_type fd
, ats_ref_type servaddr
, socklen_t salen
) {
  int err ;
  err = bind(fd, (struct sockaddr*)servaddr, salen);
  if (err < 0) {
    perror("bind");
    ats_exit_errmsg (
      EXIT_FAILURE, (ats_ptr_type)"exit(ATS): [bind] failed.\n"
    ) ; // end of [ats_exit_errmsg]
  } // end of [if]
  return ;
} // end of [atslib_bind_exn]

/* ****** ****** */

#define atslib_listen_err listen

ATSinline()
ats_void_type atslib_listen_exn (
  ats_int_type fd, ats_int_type backlog
) {
  int err = listen (fd, backlog) ;
  if (err < 0) {
    perror("listen") ;
    ats_exit_errmsg (
      EXIT_FAILURE, (ats_ptr_type)"exit(ATS): [listen] failed.\n"
    ) ; // end of [ats_exit_errmsg]
  } // end of [if]
  return ;
} // end of [atslib_listen_exn]

/* ****** ****** */

ATSinline()
ats_int_type
atslib_accept_null_err
  (ats_int_type sfd) {
  return accept(sfd, (struct sockaddr*)0, (socklen_t*)0) ;
} // end of [atslib_accept_null_err]

ATSinline()
ats_int_type
atslib_accept_null_exn (ats_int_type sfd) {
  int cfd ;
  cfd = accept(sfd, (struct sockaddr*)0, (socklen_t*)0) ;
  if (cfd < 0) {
    perror("accept");
    ats_exit_errmsg(
      EXIT_FAILURE, (ats_ptr_type)"exit(ATS): [accept] failed.\n"
    ) ; // end of [ats_exit_errmsg]
  } // end of [if]
  return cfd;
} // end of [atslib_accept_null_exn]

/* ****** ****** */

#define atslib_socket_close_err atslib_close_err

/* ****** ****** */

#define atslib_shutdown_err shutdown

/* ****** ****** */

#define atslib_socket_read_err atslib_fildes_read_err
#define atslib_socket_write_err atslib_fildes_write_err
#define atslib_socket_write_loop_err atslib_fildes_write_loop_err

/* ****** ****** */

#endif /* ATS_LIBC_SOCKET_CATS */

/* end of [socket.cats] */
