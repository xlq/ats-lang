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

#ifndef _LIBC_SOCKET_CATS
#define _LIBC_SOCKET_CATS

/* ****** ****** */

#include <errno.h>

#include <netinet/in.h>
#include <sys/socket.h>

/* ****** ****** */

// [memset] is in [string.h]
extern void *memset(void *s, int c, size_t n);

/* ****** ****** */

typedef int socket_type_t ;
typedef int address_family_t ;

static inline
ats_int_type
atslib_socket_family_type_err (address_family_t af, socket_type_t st) {
  return socket(af, st, 0) ;
}

static inline
ats_int_type
atslib_socket_family_type_exn (address_family_t af, socket_type_t st) {
  int res ;
  res = socket(af, st, 0) ;
  if (res < 0) {
    perror("socket"); ats_exit_errmsg(1, "exit(ATS): [socket] failed.\n");
  }
  return res ;
}

/* ****** ****** */

static inline
ats_void_type atslib_sockaddr_ipv4_init
  (ats_ptr_type sa0, address_family_t af, in_addr_t inp, in_port_t port) {
  struct sockaddr_in *sa = sa0 ;
  memset(sa, 0, sizeof (struct sockaddr_in)) ;
  sa->sin_family = af ;
  sa->sin_addr.s_addr = inp ;
  sa->sin_port = port ;
} /* end of [sockaddr_ipv4_init]

/* ****** ****** */

static inline
ats_int_type atslib_connect_ipv4_err
  (ats_int_type fd, ats_ref_type servaddr) {
  return connect(fd, (struct sockaddr*)servaddr, sizeof(struct sockaddr_in)) ;
}

static inline
ats_void_type atslib_connect_ipv4_exn
  (ats_int_type fd, ats_ref_type servaddr) {
  int err ;
  err = connect(fd, (struct sockaddr*)servaddr, sizeof(struct sockaddr_in)) ;
  if (err < 0) {
    perror("connect") ; ats_exit_errmsg(1, "exit(ATS): [connect] failed.\n");
  }
  return ;
}

/* ****** ****** */

static inline
ats_int_type atslib_bind_ipv4_err
  (ats_int_type fd, ats_ref_type servaddr) {
  return bind(fd, (struct sockaddr *)servaddr, sizeof(struct sockaddr_in));
} /* atslib_bind_ipv4_err */

static inline
ats_void_type atslib_bind_ipv4_exn
  (ats_int_type fd, ats_ref_type servaddr) {
  int err ;
  err = bind(fd, (struct sockaddr *)servaddr, sizeof(struct sockaddr_in));
  if (err < 0) {
    perror("bind"); ats_exit_errmsg(1, "exit(ATS): [bind] failed.\n");
  }
  return ;
} /* atslib_bind_ipv4_exn */

/* ****** ****** */

static inline
ats_int_type atslib_listen_err
  (ats_int_type fd, ats_int_type backlog) {
  return listen (fd, backlog) ;
} /* atslib_listen_err */

static inline
ats_void_type atslib_listen_exn
  (ats_int_type fd, ats_int_type backlog) {
  int err = listen (fd, backlog) ;
  if (err < 0) {
    perror("listen") ; ats_exit_errmsg(1, "exit(ATS): [listen] failed.\n") ;
  }
  return ;
} /* atslib_listen_exn */

/* ****** ****** */

static inline
ats_int_type
atslib_accept_null_err (ats_int_type fd_s) {
  return accept(fd_s, (struct sockaddr *)0, (socklen_t *)0) ;
} /* atslib_accept_null_err */

static inline
ats_int_type atslib_accept_null_exn (ats_int_type fd_s) {
  int fd_c ;
  fd_c = accept(fd_s, (struct sockaddr *)0, (socklen_t *)0) ;
  if (fd_c < 0) {
    perror("accept"); ats_exit_errmsg(1, "exit(ATS): [accept] failed.\n");
  }
  return fd_c;
} /* atslib_accept_null_exn */

//

static inline
ats_int_type atslib_accept_ipv4_exn
  (ats_int_type fd_s, ats_ref_type cliaddr, ats_ref_type addrlen) {
  int fd_c ;
  *(socklen_t *)addrlen = sizeof (struct sockaddr_in) ;
  fd_c = accept(fd_s, (struct sockaddr *)cliaddr, (socklen_t *)addrlen) ;
  if (fd_c < 0) {
    perror("accept"); ats_exit_errmsg(1, "exit(ATS): [accept] failed.\n");
  }
  return fd_c;
} /* atslib_accept_ipv4_exn */

/* ****** ****** */

static inline
ats_int_type
atslib_socket_close_err(ats_int_type fd) { return close(fd) ; }

static inline
ats_void_type
atslib_socket_close_exn(ats_int_type fd) {
  int res =  close(fd) ;
  if (res < 0) {
    perror("close") ; ats_exit_errmsg(1, "exit(ATS): [socket_close] failed.\n") ;
  }
  return ;
} /* atslib_socket_close_exn */

/* ****** ****** */

static inline
ats_ssize_type
atslib_socket_read_err
  (ats_int_type fd, ats_ptr_type buf, ats_size_type cnt) {
  return read(fd, buf, cnt) ;
} /* atslib_socket_read_err */

static inline
ats_size_type
atslib_socket_read_exn
  (ats_int_type fd, ats_ptr_type buf, ats_size_type cnt) {
  ats_ssize_type res ;
  res = read(fd, buf, cnt) ;
  if (res < 0) {
    perror("read") ; ats_exit_errmsg(1, "exit(ATS): [socket_read] failed.\n") ;
  }
  return res ;
} /* atslib_socket_read_exn */

/* ****** ****** */

static inline
ats_size_type
atslib_socket_write_exn
  (ats_int_type fd, ats_ptr_type buf, ats_size_type cnt) {
  ats_ssize_type res ;
  res = write(fd, buf, cnt) ;
  if (res < 0) {
    perror("write") ; ats_exit_errmsg(1, "exit(ATS): [socket_write] failed.\n") ;
  }
  return res ;
} /* atslib_socket_write_exn */

/* ****** ****** */

static inline
ats_ssize_type
atslib_socket_write_substring_err
  (ats_int_type fd, ats_ptr_type str, ats_size_type start, ats_size_type len)
{
  return write(fd, ((char*)str)+start, len) ;
}

static inline
ats_size_type
atslib_socket_write_substring_exn
  (ats_int_type fd, ats_ptr_type str, ats_size_type start, ats_size_type n)
{
  ats_ssize_type res ;
  res = write(fd, ((char*)str)+start, n) ;
  if (res < 0) {
    perror("write") ; ats_exit_errmsg(1, "exit(ATS): [socket_write] failed.\n") ;
  }
  return res ;
} /* ats_socket_write_substring_exn */

/* ****** ****** */

#endif /* _LIBC_SOCKET_CATS */

/* end of [socket.cats] */
