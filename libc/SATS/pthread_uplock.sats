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
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
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
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

%{#
#include "libc/CATS/pthread_uplock.cats"
%} // end of [%{#]

(* ****** ****** *)

#define ATS_STALOADFLAG 0 // no need for static loading at run-time

(* ****** ****** *)

//
// linear lock for uploading
//
absviewtype uplock_view_viewtype (int, v:view)
stadef uplock = uplock_view_viewtype

absviewtype uplockopt_view_viewtype (int, v:view)
stadef uplockopt = uplockopt_view_viewtype

absviewtype upticket_view_viewtype (v:view)
stadef upticket = upticket_view_viewtype

(* ****** ****** *)

fun pthread_uplockopt_unnone
  {v:view} (lockopt: uplockopt (0, v)): void
  = "atslib_pthread_uplockopt_unnone"
// end of [pthread_uplockopt_unnone]

//
// HX: this is really a cast function!
//
fun pthread_uplockopt_unsome
  {v:view} (lockopt: uplockopt (1, v)): uplock (1, v)
  = "atslib_pthread_uplockopt_unsome"
// end of [pthread_uplockopt_unsome]

fun pthread_uplockopt_is_none
  {v:view} {i:int} (lockopt: !uplockopt (i, v)): bool (i==0)
  = "atslib_pthread_uplockopt_is_none"
// end of [pthread_uplockopt_is_none]

fun pthread_uplockopt_is_some
  {v:view} {i:int} (lockopt: !uplockopt (i, v)): bool (i==1)
  = "atslib_pthread_uplockopt_is_some"
// end of [pthread_uplockopt_is_some]

(* ****** ****** *)

fun pthread_uplock_create
  {v:view} (): uplock (0, v) = "atslib_pthread_uplock_create"
// end of [pthread_uplock_create]

fun pthread_upticket_create
  {v:view} (lock: !uplock (0, v) >> uplock (1, v)): upticket (v)
  = "atslib_pthread_upticket_create"
// end of [pthread_upticket_create]

fun pthread_upticket_upload_and_destroy
  {v:view} (pf: v | ticket: upticket v): void
  = "atslib_pthread_upticket_upload_and_destroy"
// end of [pthread_upticket_upload_and_destroy]

(* ****** ****** *)

fun pthread_uplock_download
  {v:view} (lock: uplock (1, v)): @(v | void)
  = "atslib_pthread_uplock_download"
// end of [pthread_uplock_download]

(*
// HX-2010-10-06: this one seems of little use
fun pthread_uplock_download_try {v:view}
  (lock: uplock (1, v)): [i:two] (option_v (v, i==0) | uplockopt (i, v))
  = "atslib_pthread_uplock_download_try"
*)

(* ****** ****** *)

(* end of [pthread_uplock.sats] *)
