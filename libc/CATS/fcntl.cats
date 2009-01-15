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

#ifndef ATS_LIBC_FCNTL_CATS
#define ATS_LIBC_FCNTL_CATS

/* ****** ****** */

#include <fcntl.h>

/* ****** ****** */

#include "libc/sys/CATS/types.cats"

/* ****** ****** */

// declared in [unistd.h]
extern ssize_t read  (int fd, void *buf, size_t cnt) ;
extern ssize_t write  (int fd, const void *buf, size_t cnt) ;

/* ****** ****** */

static inline
ats_int_type
atslib_lor_flag_orflag
  (ats_int_type flag, ats_int_type orflag) {
  return (flag | orflag) ;
} /* end of [atslib_lor_flag_orflag] */

/* ****** ****** */

static inline
ats_int_type
atslib_open_flag_err
  (ats_ptr_type path, ats_int_type flag)
{
  return open((char*)path, flag) ;
} /* end of [atslib_open_flag_err] */

static inline
ats_int_type
atslib_open_flag_mode_err
  (ats_ptr_type path, ats_int_type flag, ats_int_type mode)
{
  return open((char*)path, flag, mode) ;
} /* end of [atslib_open_flag_mode_err] */

/* ****** ****** */

static inline
ats_int_type
atslib_open_flag_exn
  (ats_ptr_type path, ats_int_type flag)
{
  int fd = open((char*)path, flag) ;
  if (fd < 0) {
    perror ("open") ;
    ats_exit_errmsg(1, "exit(ATS): [open_flag] failed.\n") ;
  } // end of [if]
  return fd ;
} /* end of [atslib_open_flag_exn] */

static inline
ats_int_type
atslib_open_flag_mode_exn
  (ats_ptr_type path, ats_int_type flag, ats_mode_type mode)
{
  int fd = open((char*)path, flag, mode) ;
  if (fd < 0) {
    perror ("open") ;
    ats_exit_errmsg(1, "exit(ATS): [open_flag_mode] failed.\n") ;
  } // end of [if]
  return fd ;
} /* end of [atslib_open_flag_mode_exn] */

/* ****** ****** */

static inline
ats_int_type
atslib_close_err (ats_int_type fd) { return close(fd) ; }

static inline
ats_void_type
atslib_close_exn (ats_int_type fd) {
  int err = close(fd) ;
  if (err < 0) {
    perror ("close") ;
    ats_exit_errmsg (1, "exit(ATS): [close] failed\n") ;
  }
  return ;
} /* end of [atslib_close_exn] */

/* ****** ****** */

static inline
ats_ssize_type
atslib_fildes_read_err
  (ats_int_type fd, ats_ptr_type buf, ats_size_type cnt) {
  return read(fd, buf, cnt) ;
} /* atslib_fildes_read_err */

static inline
ats_size_type
atslib_fildes_read_exn
  (ats_int_type fd, ats_ptr_type buf, ats_size_type cnt) {
  ats_ssize_type res ;
  res = read(fd, buf, cnt) ;
  if (res < 0) {
    perror("read") ; ats_exit_errmsg(1, "Exit: [fildes_read] failed.\n") ;
  }
  return res ;
} /* atslib_fildes_read_exn */

/* ****** ****** */

static inline
ats_ssize_type
atslib_fildes_write_err
  (ats_int_type fd, ats_ptr_type buf, ats_size_type cnt) {
  return write(fd, buf, cnt) ;
} /* atslib_fildes_write_err */

static inline
ats_size_type
atslib_fildes_write_exn
  (ats_int_type fd, ats_ptr_type buf, ats_size_type cnt) {
  ats_ssize_type res ;
  res = write(fd, buf, cnt) ;
  if (res < 0) {
    perror("write") ; ats_exit_errmsg(1, "Exit: [fildes_write] failed.\n") ;
  }
  return res ;
} /* atslib_fildes_write_exn */

/* ****** ****** */

static inline
ats_ssize_type
atslib_fildes_write_substring_err
  (ats_int_type fd, ats_ptr_type str, ats_size_type start, ats_size_type n)
{
  return write(fd, ((char*)str)+start, n) ;
}

static inline
ats_size_type
atslib_fildes_write_substring_exn
  (ats_int_type fd, ats_ptr_type str, ats_size_type start, ats_size_type n)
{
  ats_ssize_type res ;
  res = write(fd, ((char*)str)+start, n) ;
  if (res < 0) {
    perror("write") ; ats_exit_errmsg(1, "exit(ATS): [fildes_write] failed.\n") ;
  }
  return res ;
} /* ats_fildes_write_substring_exn */

/* ****** ****** */

#endif /* ATS_LIBC_FCNTL_CATS */
