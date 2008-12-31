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

static inline
ats_int_type
atslib_open_path_flag_err
  (ats_ptr_type path, ats_int_type flag)
{
  return open((char*)path, flag) ;
} /* end of [atslib_open_path_flag_err]

static inline
ats_int_type
atslib_open_path_flag_mode_err
  (ats_ptr_type path, ats_int_type flag, ats_int_type mode)
{
  return open((char*)path, flag, mode) ;
} /* end of [atslib_open_path_flag_mode_err]

/* ****** ****** */

static inline
ats_int_type
atslib_close_err (ats_int_type fd) { return close(fd) ; }

/* ****** ****** */

#endif /* ATS_LIBC_FCNTL_CATS */
