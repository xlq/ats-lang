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

typedef int socket_domain_t ;
typedef int socket_type_t ;

static inline
ats_int_type
atslib_socket_domain_type_err (socket_domain_t sd, socket_type_t st) {
  return socket(sd, st, 0) ;
}

static inline
ats_int_type
atslib_socket_domain_type_exn (socket_domain_t sd, socket_type_t st) {
  int res ;
  res = socket(sd, st, 0) ;
  if (res < 0) {
    perror("socket"); ats_exit_errmsg(1, "Exit: [socket] failed.\n");
  }
  return res ;
}

/* ****** ****** */

// [memset] is in [string.h]
extern void *memset(void *s, int c, size_t n);

static inline
ats_int_type
atslib_bind_inet_any_port_err
  (ats_int_type fd, ats_int_type port) {
  int res ;
  struct sockaddr_in *server_addr ;

  server_addr = malloc(sizeof(struct sockaddr_in));
  if (!server_addr) {
    ats_exit_errmsg(1, "Exit: [bind] failed: no memory.\n") ;
  }
  
  memset((char*)server_addr, 0, sizeof(struct sockaddr_in)) ;
  server_addr->sin_family = AF_INET;
  server_addr->sin_addr.s_addr = INADDR_ANY;
  server_addr->sin_port = htons(port);

  res = bind(fd, (struct sockaddr *)server_addr, sizeof(struct sockaddr_in));

  if (res < 0) free(server_addr) ;

  return res ;
} /* atslib_bind_inet_any_port_err */

static inline
ats_void_type
atslib_bind_inet_any_port_exn
  (ats_int_type fd, ats_int_type port) {
  int res ;
  res = atslib_bind_inet_any_port_err(fd, port) ;
  if (res < 0) {
    perror("bind"); ats_exit_errmsg(1, "Exit: [bind] failed.\n");
  }
  return ;
} /* atslib_bind_inet_any_port_exn */

//

static inline
ats_int_type
atslib_listen_err
  (ats_int_type fd, ats_int_type backlog) {
  return listen (fd, backlog) ;
}

static inline
ats_void_type
atslib_listen_exn
  (ats_int_type fd, ats_int_type backlog) {
  int res = listen (fd, backlog) ;
  if (res < 0) {
    perror("listen") ;
    ats_exit_errmsg(1, "Exit: [listen] failed.\n") ;
  }
  return ;
} /* atslib_listen_exn */

//

static inline
ats_int_type
atslib_accept_inet_err(ats_int_type fd) {
  struct sockaddr_in *client_addr ;
  client_addr = (struct sockaddr_in *) malloc(sizeof(struct sockaddr_in));

  if (!client_addr) {
    ats_exit_errmsg(1, "Exit: [accept] failed: no memory.\n") ;
  }

  socklen_t client_addrlen = sizeof(struct sockaddr_in) ;
  int res = accept(fd, (struct sockaddr *) client_addr, &client_addrlen) ;
  if (res < 0) free(client_addr) ;
  return res;
}

static inline
ats_int_type
atslib_accept_inet_exn (ats_int_type fd) {
  int res ;
  res = atslib_accept_inet_err(fd) ;
  if (res < 0) {
    perror("accept"); ats_exit_errmsg(1, "Exit: [accept] failed.\n");
  }
  return res ;
} /* atslib_accept_inet_exn */

//

static inline
ats_int_type
atslib_socket_close_err(ats_int_type fd) { return close(fd) ; }

static inline
ats_void_type
atslib_socket_close_exn(ats_int_type fd) {
  int res =  close(fd) ;
  if (res < 0) {
    perror("close") ;
    ats_exit_errmsg(1, "Exit: [socket_close] failed.\n") ;
  }
  return ;
} /* atslib_socket_close_exn */

//

static inline
ats_int_type
atslib_socket_read_err
  (ats_int_type fd, ats_ptr_type buf, ats_int_type cnt) {
  return read(fd, buf, cnt) ;
}

static inline
ats_int_type
atslib_socket_read_exn
  (ats_int_type fd, ats_ptr_type buf, ats_int_type cnt) {
  int res ;
  res = read(fd, buf, cnt) ;
  if (res < 0) {
    perror("read") ;
    ats_exit_errmsg(1, "Exit: [socket_read] failed.\n");
  }
  return res ;
} /* atslib_socket_read_exn */

//

static inline
ats_int_type
atslib_socket_write_err
  (ats_int_type fd, ats_ptr_type buf, ats_int_type cnt) {
  return write(fd, buf, cnt) ;
}

static inline
ats_int_type
atslib_socket_write_exn
  (ats_int_type fd, ats_ptr_type buf, ats_int_type cnt) {
  int res ;
  res = write(fd, buf, cnt) ;
  if (res < 0) {
    perror("write") ;
    ats_exit_errmsg(1, "Exit: [socket_write] failed.\n");
  }
  return res ;
} /* atslib_socket_write_exn */

//

static inline
ats_int_type
ats_socket_write_substring_err
  (ats_int_type fd, ats_ptr_type s, ats_int_type start, ats_int_type n)
{
  return write(fd, ((char*)s)+start, n) ;
}

static inline
ats_int_type
ats_socket_write_substring_exn
  (ats_int_type fd, ats_ptr_type s, ats_int_type start, ats_int_type n)
{
  int res ;
  res = write(fd, ((char*)s)+start, n) ;
  if (res < 0) {
    perror("write") ; ats_exit_errmsg(1, "Exit: [socket_write] failed.\n");
  }
  return res ;
} /* ats_socket_write_substring_exn */

/* ****** ****** */

#endif /* _LIBC_SOCKET_CATS */

/* end of [socket.cats] */
