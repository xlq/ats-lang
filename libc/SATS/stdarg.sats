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

#include "libc/CATS/stdarg.cats"

%}

(* ****** ****** *)

absviewt@ype va_list (ts: types) = $extype "va_list"
absviewt@ype va_list1 (t: t@ype, ts: types) = $extype "va_list"

(* ****** ****** *)

typedef va_arg_type (t:t@ype) =
  {ts:types} (&va_list1 (t, ts) >> va_list ts) -<> t
// ...

fun{t:t@ype} va_arg : va_arg_type (t)

fun va_arg_int : va_arg_type (int) = "atslib_va_arg_int"
fun va_arg_ptr : va_arg_type (ptr) = "atslib_va_arg_ptr"

fun va_arg_bool : va_arg_type (bool) = "atslib_va_arg_bool"
fun va_arg_char : va_arg_type (char) = "atslib_va_arg_char"

fun va_arg_string
  : va_arg_type (string) = "atslib_va_arg_ptr"
// end of ...

(* ****** ****** *)

(*

fun va_start ...

fun va_end {ts:types} (ap: va_list ts):<> void
  = "atslib_va_end"

*)

(* ****** ****** *)

fun va_copy {ts:types}
  (dst: &va_list? >> va_list ts, src: va_list ts):<> void
  = "atslib_va_copy"

(* ****** ****** *)

(* end of [stdarg.sats] *)
