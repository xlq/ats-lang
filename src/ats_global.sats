(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS/Anairiats - Unleashing the Potential of Types!
 *
 * Copyright (C) 2002-2008 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
 * Free Software Foundation; either version 3, or (at  your  option)  any
 * later version.
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
 *)

(* ****** ****** *)

// Time: July 2007
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

(* ****** ****** *)

(* ats_global: handling some global variables *)

(* ****** ****** *)

fun ats_function_name_prefix_get (): Stropt
  = "ats_global_ats_function_name_prefix_get"

fun ats_function_name_prefix_set (prfx: Stropt): void
  = "ats_global_ats_function_name_prefix_set"

(* ****** ****** *)

fun ats_dynloadflag_get (): int
  = "ats_global_ats_dynloadflag_get"

fun ats_dynloadflag_set (flag: int): void
  = "ats_global_ats_dynloadflag_set"

(* ****** ****** *)

fun ats_dynloadfuname_get (): Stropt
  = "ats_global_ats_dynloadfuname_get"

fun ats_dynloadfuname_set (name: Stropt): void
  = "ats_global_ats_dynloadfuname_set"

(* ****** ****** *)

fun ats_depgenflag_get (): int
  = "ats_global_ats_depgenflag_get"

fun ats_depgenflag_set (flag: int): void
  = "ats_global_ats_depgenflag_set"

(* ****** ****** *)

(* end of [ats_global.sats] *)
