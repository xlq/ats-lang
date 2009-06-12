(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Anairiats - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
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

// Time: October 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* ats_debug: some functions for debugging *)

(* ****** ****** *)

fun debug_flag_get ():<!ref> int = "ats_debug_flag_get"
fun debug_flag_set (i: int):<!ref> void = "ats_debug_flag_set"

fun debug_prerrf {ts:types} (fmt: printf_c ts, arg: ts):<!exnref> void
  = "ats_debug_prerrf"

fun debug_printf {ts:types} (fmt: printf_c ts, arg: ts):<!exnref> void
  = "ats_debug_printf"

(* ****** ****** *)

(* end of [ats_debug.sats] *)
