(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
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
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // loaded by [ats_main_prelude]

(* ****** ****** *)

%{

ats_void_type atspre_exit_prerrf
  (const ats_int_type status, const ats_ptr_type fmt, ...)
{
  va_list ap ;
  va_start(ap, fmt) ; vfprintf(stderr, (char*)fmt, ap) ; va_end(ap) ;
/*
  fprintf (stderr, "atspre_exit_prerrf: status = %i\n", status) ;
*/
  exit(status) ;
  return ; // deadcode
} /* end of [atspre_exit_prerrf] */

ats_void_type atspre_assert_prerrf
  (ats_bool_type assertion, ats_ptr_type fmt, ...) {
  int err ;
  va_list ap ;

  if (!assertion) { /* assertion is false */
    va_start(ap, fmt) ;
    err = vfprintf(stderr, (char*)fmt, ap) ;
    va_end(ap) ;
    if (err < 0) {
      ats_exit_errmsg (
        err, "[atspre_assert_prerrf]: prerrf failed\n"
      ) ;
    } else {
      ats_exit_errmsg (1, "[atspre_assert_prerrf]: assert failed\n") ;
    }
  } /* end of [if] */

  return ;
} /* end of [atspre_assert_prerrf] */

%} // end of [%{]

(* ****** ****** *)

%{

// functions for sprintf

static
ats_ptr_type __tostringf_size
  (const ats_int_type guess, const ats_ptr_type fmt, va_list ap0)
{
  int n, sz ; char *res ; va_list ap ;

  sz = guess ;

  while (1) {
    va_copy (ap, ap0) ;
    res = ATS_MALLOC(sz) ;
    n = vsnprintf(res, sz, (char*)fmt, ap) ;
    if (n >= 0) {
      if (n < sz) return res ;
      sz = n+1 ; ATS_FREE(res) ; continue ;
    } else {
      return ((ats_ptr_type)0) ;
    } // end of [if]
  } // end of [while]

  return (ats_ptr_type)0 ; // deadcode

} /* end of [__tostringf_size] */

ats_ptr_type atspre_tostringf_size
  (const ats_int_type guess, const ats_ptr_type fmt, ...)
{
  char *res ;
  va_list ap ;

  va_start(ap, fmt);
  res = (char*)__tostringf_size (guess, fmt, ap);
  va_end(ap);
  if (!res) {
    ats_exit_errmsg (1, "Exit: [ats_tostringf_size] failed.\n") ;
  }
  return res ;
} /* end of [atspre_tostringf_size] */

#define __TOSTRINGF_GUESS 16
ats_ptr_type
atspre_tostringf (ats_ptr_type fmt, ...) {
  char *res ;
  va_list ap ;

  va_start(ap, fmt);
  res = (char*)__tostringf_size (__TOSTRINGF_GUESS, fmt, ap);
  va_end(ap);

  if (!res) {
    ats_exit_errmsg (1, "Exit: [ats_tostringf] failed.\n") ;
  }

  return res ;
} /* end of [atspre_tostringf] */

%}

(* ****** ****** *)

(* end of [printf.dats] *)
